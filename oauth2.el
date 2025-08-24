;;; oauth2.el --- OAuth 2.0 Authorization Protocol  -*- lexical-binding:t -*-

;; Copyright (C) 2011-2021 Free Software Foundation, Inc

;; Author: Julien Danjou <julien@danjou.info>
;; Version: 0.17
;; Keywords: comm
;; Package-Requires: ((cl-lib "0.5") (nadvice "0.3"))

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; Implementation of the OAuth 2.0 draft.
;;
;; The main entry point is `oauth2-auth-and-store' which will return a token
;; structure.  This token structure can be then used with
;; `oauth2-url-retrieve-synchronously' or `oauth2-url-retrieve' to retrieve
;; any data that need OAuth authentication to be accessed.
;;
;; If the token needs to be refreshed, the code handles it automatically and
;; store the new value of the access token.

;;; Code:

(eval-when-compile (require 'cl-lib))
(require 'plstore)
(require 'json)
(require 'url-http)

(defvar url-http-data)
(defvar url-http-method)
(defvar url-http-extra-headers)
(defvar url-callback-arguments)
(defvar url-callback-function)

(defgroup oauth2 nil
  "OAuth 2.0 Authorization Protocol."
  :group 'comm
  :link '(url-link :tag "Savannah" "https://git.savannah.gnu.org/cgit/emacs/elpa.git/tree/?h=externals/oauth2")
  :link '(url-link :tag "ELPA" "https://elpa.gnu.org/packages/oauth2.html"))

(defvar oauth2-debug nil
  "Enable verbose logging in oauth2 to help debugging.")

(defvar oauth2--default-redirect-uri "urn:ietf:wg:oauth:2.0:oob"
  "Default redirect URI for OAuth2 authorization.")

(defun oauth2--do-debug (&rest msg)
  "Output debug messages when `oauth2-debug' is enabled.
MSG is a list of format string and arguments passed to `message'."
  (when oauth2-debug
    (setcar msg (concat "[oauth2] " (car msg)))
    (apply #'message msg)))

(defun oauth2--current-timestamp ()
  "Return the current time in Emacs internal time format."
  (current-time))

(defun oauth2--build-url-param-str (&rest data)
  "Build URL data string with values in DATA.
DATA should be a list of attribute name and value pairs -- each value will
be hexified to be URL-safe.  If a value is not a string or an empty
string, this pair of key value will be skipped.

Return a URL-safe string of parameter data."
  (cl-assert (= (mod (length data) 2) 0) t
             "Invalid parameters.  Must be attribute name value pairs.")
  (let (data-list)
    (while data
      (let ((key (pop data))
            (value (pop data)))
        (when (and (stringp value)
                   (not (string-empty-p value)))
          (add-to-list 'data-list
                       (concat key "=" (url-hexify-string value))
                       t))))
    (url-encode-url (string-join data-list "&"))))

(defun oauth2--build-url (address &rest data)
  "Build a URL string with ADDRESS and DATA.
DATA can be a string or an alist of attributes.  If it is a string, it
will be encoded; if it is an alist it will be converted to a URL-safe
string using `oauth2--build-url-param-str'.  It will then be combined with
ADDRESS to build the full URL."
  (let ((data-str (progn
                    (if (> (length data) 1)
                        (apply 'oauth2--build-url-param-str
                               data)
                      (url-encode-url (car data))))))
    (concat address "?" data-str)))

(defun oauth2--generate-code-verifier (&optional verifier-length)
  "Generate a random string of VERIFIER-LENGTH long for code_challenge.
The string should be of length 43 to 128 (inclusive).  If
VERIFIER-LENGTH is nil, default to 90 as mutt_oauth2.py did.  See
RFC7636 for more details."
  (let* ((func-name "oauth2--generate-code-verifier")
         (valid-chars
          "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_")
         (verifier-length (or verifier-length 90))
         result-list)
    (dotimes (_ verifier-length)
      (let ((i (random (length valid-chars))))
        (push (substring valid-chars i (1+ i)) result-list)))
    (base64url-encode-string (string-join result-list))))

(defun oauth2--get-challenge-from-verifier (code-verifier)
  "Get the code_challenge from CODE-VERIFIER.
Returns a base64url-encoded SHA256 hash of CODE-VERIFIER."
  ;; base64url-encode-string returns a string that ends with '=' so the last
  ;; character should be skipped.
  (substring (base64url-encode-string (secure-hash 'sha256
                                                   code-verifier
                                                   nil nil t))
             0 -1))

(defun oauth2-request-authorization (auth-url client-id &optional scope state redirect-uri user-name code-verifier)
  "Request OAuth authorization at AUTH-URL by launching `browse-url'.
CLIENT-ID is the client id provided by the provider.
Optional SCOPE specifies the access scope requested.
Optional STATE provides additional security against CSRF attacks.
Optional REDIRECT-URI specifies where to redirect after authorization.
Optional USER-NAME is used to provide the login_hint which will fill
the login user name on the requesting webpage to save users some typing.
Optional CODE-VERIFIER enables PKCE (Proof Key for Code Exchange).

Return the authorization code provided by the service."
  (let* ((func-name "oauth2-request-authorization")
         (url-params (list "client_id" client-id
                           "response_type" "code"
                           "redirect_uri" (or redirect-uri oauth2--default-redirect-uri)
                           "scope" scope
                           "state" state
                           "login_hint" user-name
                           "access_type" "offline"
                           "prompt" "consent")))
    (when (and code-verifier
               (not (string-empty-p code-verifier)))
      (setq url-params (append url-params
                               (list "code_challenge" (oauth2--get-challenge-from-verifier code-verifier)
                                     "code_challenge_method" "S256"))))
    (let ((url (apply 'oauth2--build-url auth-url url-params)))
      (oauth2--do-debug "[%s]: url: %s" func-name url)
      (browse-url url)
      (read-string (concat "Follow the instruction on your default browser, or "
                           "visit:\n" url
                           "\nEnter the code your browser displayed: ")))))

(defun oauth2-request-access-parse ()
  "Parse the result of an OAuth request."
  (goto-char (point-min))
  (when (search-forward-regexp "^$" nil t)
    (json-read)))

(defun oauth2-make-access-request (url data)
  "Make an access request to URL using DATA, returning parsed JSON response."
  (let ((func-name (nth 1 (backtrace-frame 3))))
    (oauth2--do-debug "%s: url: %s" func-name url)
    (oauth2--do-debug "%s: data: %s" func-name data)
    (let ((url-request-method "POST")
          (url-request-data data)
          (url-request-extra-headers
           '(("Content-Type" . "application/x-www-form-urlencoded"))))
      (with-current-buffer (url-retrieve-synchronously url)
        (let ((data (oauth2-request-access-parse)))
          (kill-buffer (current-buffer))
          (oauth2--do-debug "[%s]: response: %s" func-name (prin1-to-string data))
          data)))))

(cl-defstruct oauth2-token
  plstore
  plstore-id
  client-id
  client-secret
  access-token
  refresh-token
  request-timestamp
  code-verifier
  auth-url
  token-url
  access-response)

(defun oauth2-request-access (token-url client-id client-secret code &optional redirect-uri host-name code-verifier)
  "Request OAuth access at TOKEN-URL.
CLIENT-ID and CLIENT-SECRET identify the application.
The CODE should be obtained with `oauth2-request-authorization'.
Optional REDIRECT-URI should match the one used in authorization.
Optional HOST-NAME is currently unused.
Optional CODE-VERIFIER is used for the PKCE extension and is required
when it was already provided during authorization.

Return an `oauth2-token' structure."
  (when code
    (let* ((request-timestamp (oauth2--current-timestamp))
           (access-response (oauth2-make-access-request
                             token-url
                             (oauth2--build-url-param-str
                              "client_id" client-id
                              "client_secret" client-secret
                              "code" code
                              "code_verifier" code-verifier
                              "redirect_uri" (or redirect-uri
                                                 oauth2--default-redirect-uri)
                              "grant_type" "authorization_code"))))
      (make-oauth2-token :client-id client-id
                         :client-secret client-secret
                         :access-token (cdr (assoc 'access_token access-response))
                         :refresh-token (cdr (assoc 'refresh_token access-response))
                         :code-verifier code-verifier
                         :auth-url auth-url
                         :token-url token-url
                         :access-response access-response))))

;;;###autoload
(defun oauth2-refresh-access (token &optional host-name)
  "Refresh OAuth access TOKEN.
TOKEN should be obtained with `oauth2-request-access'.
Optional HOST-NAME is currently unused.
Updates the TOKEN in-place with the new access token and returns it."
  (let* ((client-id (oauth2-token-client-id token))
         (client-secret (oauth2-token-client-secret token))
         (refresh-token (oauth2-token-refresh-token token))
         (token-url (oauth2-token-token-url token))
         (url-param-str (oauth2--build-url-param-str
                         "client_id" client-id
                         "client_secret" client-secret
                         "refresh_token" refresh-token
                         "grant_type" "refresh_token"))
         (access-token (cdr (assoc 'access_token
                                   (oauth2-make-access-request
                                    token-url url-param-str)))))
    (setf (oauth2-token-request-timestamp token) (oauth2--current-timestamp))
    (setf (oauth2-token-access-token token) access-token))
  ;; If the token has a plstore, update it
  (let ((plstore (oauth2-token-plstore token)))
    (when plstore
      (plstore-put plstore (oauth2-token-plstore-id token)
                   nil `(:access-token
                         ,(oauth2-token-access-token token)
                         :refresh-token
                         ,(oauth2-token-refresh-token token)
                         :access-response
                         ,(oauth2-token-access-response token)
                         ))
      (plstore-save plstore)))
  token)

;;;###autoload
(defun oauth2-auth (auth-url token-url client-id client-secret &optional scope state redirect-uri user-name host-name code-verifier)
  "Authenticate application via OAuth2.
AUTH-URL is the authorization endpoint URL.
TOKEN-URL is the token endpoint URL.
CLIENT-ID and CLIENT-SECRET identify the application.
Optional SCOPE specifies the access scope requested.
Optional STATE provides additional security against CSRF attacks.
Optional REDIRECT-URI specifies where to redirect after authorization.
Optional USER-NAME provides a login hint for the authorization page.
Optional HOST-NAME is currently unused.
Optional CODE-VERIFIER enables PKCE (Proof Key for Code Exchange).

Return an `oauth2-token' structure."
  (oauth2-request-access
   token-url
   client-id
   client-secret
   (oauth2-request-authorization
    auth-url client-id scope state redirect-uri user-name code-verifier)
   redirect-uri
   host-name
   code-verifier))

(defcustom oauth2-token-file (locate-user-emacs-file "oauth2.plstore")
  "File path where OAuth tokens are stored."
  :group 'oauth2
  :type 'file)

(defun oauth2-compute-id (auth-url token-url scope client-id user-name)
  "Compute a unique id mainly to use as plstore id.
The result is computed using AUTH-URL, TOKEN-URL, SCOPE, CLIENT-ID, and
USER-NAME to ensure the plstore id is unique."
  (secure-hash 'sha512 (concat auth-url token-url scope client-id user-name)))

;;;###autoload
(defun oauth2-auth-and-store (auth-url token-url scope client-id client-secret &optional redirect-uri state user-name host-name use-pkce)
  "Request access to a resource and store it using `plstore'.
AUTH-URL is the authorization endpoint URL.
TOKEN-URL is the token endpoint URL.
SCOPE specifies the access scope requested.
CLIENT-ID and CLIENT-SECRET identify the application.
Optional REDIRECT-URI specifies where to redirect after authorization.
Optional STATE provides additional security against CSRF attacks.
Optional USER-NAME provides a login hint for the authorization page.
Optional HOST-NAME is currently unused.
Optional USE-PKCE enables PKCE (Proof Key for Code Exchange).

If a token already exists for these parameters, return it.
Otherwise, perform the full OAuth2 flow and store the result.
Return an `oauth2-token' structure."
  ;; We store a MD5 sum of all URL
  (let* ((plstore (plstore-open oauth2-token-file))
         (id (oauth2-compute-id auth-url token-url scope client-id user-name))
         (plist (cdr (plstore-get plstore id))))
    ;; Check if we found something matching this access
    (if plist
        ;; We did, return the token object
        (make-oauth2-token :plstore plstore
                           :plstore-id id
                           :client-id client-id
                           :client-secret client-secret
                           :access-token (plist-get plist :access-token)
                           :refresh-token (plist-get plist :refresh-token)
                           :code-verifier (plist-get plist :code-verifier)
                           :token-url token-url
                           :access-response (plist-get plist :access-response))
      (let* ((code-verifier (if use-pkce
                                (oauth2--generate-code-verifier)
                              ""))
             (token (oauth2-auth auth-url token-url
                                 client-id client-secret scope state redirect-uri user-name host-name code-verifier)))
        ;; Set the plstore
        (setf (oauth2-token-plstore token) plstore)
        (setf (oauth2-token-plstore-id token) id)
        (plstore-put plstore id nil `(:access-token
                                      ,(oauth2-token-access-token token)
                                      :code-verifier
                                      ,(oauth2-token-code-verifier token)
                                      :refresh-token
                                      ,(oauth2-token-refresh-token token)
                                      :access-response
                                      ,(oauth2-token-access-response token)))
        (plstore-save plstore)
        token))))

(defun oauth2-url-append-access-token (token url)
  "Append access token from TOKEN to URL as a query parameter."
  (concat url
          (if (string-match-p "\?" url) "&" "?")
          "access_token=" (oauth2-token-access-token token)))

(defvar oauth--url-advice nil
  "Internal variable to control oauth2 URL advice activation.")
(defvar oauth--token-data
  "Internal variable to store token and URL data for OAuth2 requests.")

(defun oauth2-authz-bearer-header (token)
  "Return `Authorization: Bearer' header with TOKEN."
  (cons "Authorization" (format "Bearer %s" token)))

(defun oauth2-extra-headers (extra-headers)
  "Return EXTRA-HEADERS with `Authorization: Bearer' added."
  (cons (oauth2-authz-bearer-header (oauth2-token-access-token (car oauth--token-data)))
        extra-headers))

;; FIXME: We should change URL so that this can be done without an advice.
(defun oauth2--url-http-handle-authentication-hack (orig-fun &rest args)
  (if (not oauth--url-advice)
      (apply orig-fun args)
    (let ((url-request-method url-http-method)
          (url-request-data url-http-data)
          (url-request-extra-headers
           (oauth2-extra-headers url-http-extra-headers)))
      (oauth2-refresh-access (car oauth--token-data))
      (url-retrieve-internal (cdr oauth--token-data)
                             url-callback-function
                             url-callback-arguments)
      ;; This is to make `url' think it's done.
      (when (boundp 'success) (setq success t)) ;For URL library in Emacs<24.4.
      t)))                                      ;For URL library in Emacs≥24.4.
(advice-add 'url-http-handle-authentication :around
            #'oauth2--url-http-handle-authentication-hack)

;;;###autoload
(defun oauth2-url-retrieve-synchronously (token url &optional request-method request-data request-extra-headers)
  "Retrieve URL synchronously using TOKEN to access it.
TOKEN can be obtained with `oauth2-auth'.
Optional REQUEST-METHOD specifies the HTTP method (default GET).
Optional REQUEST-DATA specifies data to send in the request body.
Optional REQUEST-EXTRA-HEADERS specifies additional HTTP headers.

Return the buffer containing the response."
  (let* ((oauth--token-data (cons token url)))
    (let ((oauth--url-advice t)         ;Activate our advice.
          (url-request-method request-method)
          (url-request-data request-data)
          (url-request-extra-headers
           (oauth2-extra-headers request-extra-headers)))
      (url-retrieve-synchronously url))))

;;;###autoload
(defun oauth2-url-retrieve (token url callback &optional cbargs request-method request-data request-extra-headers)
  "Retrieve URL asynchronously using TOKEN to access it.
TOKEN can be obtained with `oauth2-auth'.
CALLBACK gets called with CBARGS when finished.  See `url-retrieve'.
Optional REQUEST-METHOD specifies the HTTP method (default GET).
Optional REQUEST-DATA specifies data to send in the request body.
Optional REQUEST-EXTRA-HEADERS specifies additional HTTP headers."
  ;; TODO add support for SILENT and INHIBIT-COOKIES.  How to handle this in `url-http-handle-authentication'.
  (let* ((oauth--token-data (cons token url)))
    (let ((oauth--url-advice t)         ;Activate our advice.
          (url-request-method request-method)
          (url-request-data request-data)
          (url-request-extra-headers
           (oauth2-extra-headers request-extra-headers)))
      (url-retrieve url callback cbargs))))

(provide 'oauth2)

;;; oauth2.el ends here
