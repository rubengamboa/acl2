; XDOC Utilities -- An Extension of DEFXDOC
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defxdoc+
  :parents (xdoc-utilities)
  :short "@('defxdoc+') extends @(tsee defxdoc) with some conveniences."
  :long
  "<p>
   In addition to the arguments of @(tsee defxdoc),
   @('defxdoc+') takes the following keyword arguments:
   </p>
   <ul>
     <li>
     @(':order-subtopics'), which must be @('t') or @('nil').
     If it is @('t'),
     a call of @(tsee xdoc::order-subtopics) is generated
     to order all the subtopics of this topic.
     </li>
     <li>
     @(':default-parent'), which must be @('t') or @('nil').
     If it is @('t'),
     a book-@(see local) call of @(tsee set-default-parents) is generated
     to use the singletong list of this topic as default parents.
     </li>
   </ul>
   @(def defxdoc+)"

  (defmacro defxdoc+ (&rest args)
    (let* ((name (car args))
           (keyargs (cdr args))
           (parents (cadr (assoc-keyword :parents keyargs)))
           (short (cadr (assoc-keyword :short keyargs)))
           (long (cadr (assoc-keyword :long keyargs)))
           (pkg (cadr (assoc-keyword :pkg keyargs)))
           (no-override (cadr (assoc-keyword :no-override keyargs)))
           (order-subtopics (cadr (assoc-keyword :order-subtopics keyargs)))
           (default-parent (cadr (assoc-keyword :default-parent keyargs))))
      `(progn
         (defxdoc ,name
           :parents ,parents
           :short ,short
           :long ,long
           :pkg ,pkg
           :no-override ,no-override)
         ,@(and order-subtopics
                `((xdoc::order-subtopics ,name nil t)))
         ,@(and default-parent
                `((local (set-default-parents ,name))))))))
