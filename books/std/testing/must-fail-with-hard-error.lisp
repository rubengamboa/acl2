; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-fail")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-hard-error

  :parents (std/testing errors must-fail)

  :short "A specialization of @(tsee must-fail) to ensure that
          a hard error occurs."

  :long

  "<p>Evaluation of @('(must-fail-with-hard-error <form>)') returns
   without error exactly when evaluation of @('<form>') causes a hard error.</p>

   <p>See @(see must-fail) for more details, as @('must-fail-with-hard-error')
   abbreviates @('must-fail') as follows.</p>

   @(def must-fail-with-hard-error)

   <p>Also see @(see must-fail-with-error) and
   @(see must-fail-with-soft-error).</p>"

  (defmacro must-fail-with-hard-error (form &rest args)
    (list* 'must-fail form :expected :hard args)))
