#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "cgen/top" :ttags :all)
(include-book "utilities")
(include-book "kestrel/utilities/symbols" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "centaur/misc/outer-local" :dir :system)

#|
Here is the top-level defunc control flow:

Test phase:
  skip-proofs defun
  If test? function-contract fails
    return message; quit
  ;;skip-proofs (function-contract)
  ;;maybe function-contract fails
  If test? body-contracts fails
    return message; quit

Logic-mode or program-mode?
  If function terminates then logic-mode else program-mode

Program-mode
 defun/program-mode; fail /or :success

Logic-mode
  FC: Function-contract holds?
  If FC then
     defun-ng/static; FC;
      BC: body contracts hold?
      if BC then verify-guards
      else
       message+= check: defun-ng/static; FC; verify-guard. defun, FC should pass &
                 verify-guard should fail;
       fail /or :success
  else
    message+=check: defun-ng; FC, defun should pass, FC will fail;
    fail /or defun-ng/dynamic;
    BC: dynamic-body contracts hold?
    if BC then verify-guards; :success
    else
      message+= check: defun-ng/dynamic; FC, verify-guards. Only defun passes;
      fail /or :success


Here is one way of encoding the above flow using nested make-event with :OR
Let termination-strictp, function-contract-strictp and body-contracts-strictp be defined in a table (or globally).

(make-event
 (er-progn
   (test-phase ...)
   (cond ((and termination-strictp function-contract-strictp)
           `(:OR ,(static-defunc-events ...)
                 ,(make-show-failure-msg-ev ...)))
          (termination-strictp
           `(:OR ,(static-defunc-events ...)
                 ,(dynamic-defunc-events ...)
                 ,(make-show-failure-msg-ev ...)))
          (t `(:OR ,(static-defunc-events ...)
                   ,(dynamic-defunc-events ...)
                   ,(program-mode-defunc-events ...)
                   ,(make-show-failure-msg-ev ...))))))
||#

(defdata-alias bool boolean)
(defdata-alias int integer)
(defdata-alias tl true-list)

#!ACL2
(defun function-guard-obligation (fun-name state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* (((mv cl-set &) (guard-clauses-for-clique (list fun-name)
                                                T ;debug-p
                                                (ens state)
                                                (w state)
                                                (f-get-global 'safe-mode state)
                                                (gc-off state)
                                                nil))
       (guard-ob (prettyify-clause-set cl-set (let*-abstractionp state) (w state)))
       ;;(- (cw "fn: ~x0 and body-contract-obligation: ~x1~%" fun-name guard-ob))
       )
    (value guard-ob)))



(mutual-recursion
 (defun simple-termp (x)
   (declare (xargs :guard t))
   (cond ((atom x) t)
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cdr (cdr x)))))
         ((not (true-listp x)) nil)
         ((not (simple-term-listp (cdr x))) nil)
         (t (or (symbolp (car x))
                (and (true-listp (car x))
                     (equal (length (car x)) 3)
                     (eq (car (car x)) 'lambda)
                     (symbol-listp (cadr (car x)))
                     (simple-termp (caddr (car x)))
                     (equal (length (cadr (car x)))
                            (length (cdr x))))))))

 (defun simple-term-listp (lst)
   (declare (xargs :guard t))
   (cond ((atom lst) (equal lst nil))
         (t (and (simple-termp (car lst))
                 (simple-term-listp (cdr lst)))))))

(defun xargs-kwd-alist1 (decls keywords ctx al)
  (if (atom decls)
      al
    (if (and (consp (car decls))
             (eq 'acl2::declare (caar decls))
             (consp (cdr (car decls)))
             (consp (cadr (car decls)))
             (eq 'acl2::xargs (first (cadr (car decls)))))
        (b* ((kwd-val-list (cdr (cadr (car decls))))
             ((mv al ?rest-args) (extract-keywords ctx keywords kwd-val-list al)))
          (xargs-kwd-alist1 (cdr decls) keywords ctx al))
      (xargs-kwd-alist1 (cdr decls) keywords ctx al))))

(defconst *our-xargs-keywords*
  (append '(:CONSIDER-CCMS :CONSIDER-ONLY-CCMS :TERMINATION-METHOD
                           :CCG-PRINT-PROOFS :TIME-LIMIT
                           :CCG-HIERARCHY)
          acl2::*xargs-keywords*))

(defun xargs-kwd-alist (decls ctx)
  "Parse a list of declare forms into a kwd-alist mapping xarg keywords to their values."
  (xargs-kwd-alist1 decls *our-xargs-keywords* ctx nil))

#!ACL2
(verify-termination find-runed-lemma (declare (xargs :measure (if (null lst) 0 (1+ (acl2-count lst))))))

;returns controller pocket
#!ACL2
(defun controller-alist (nm wrld)
  (if (and (not (symbolp nm))
           (not (function-symbolp nm wrld)))
      nil
    (let ((rl (find-runed-lemma `(:definition ,nm)
                                (getprop nm 'lemmas nil 'current-acl2-world wrld))))
      (if rl
          (let ((ctrl-pocket
                 (cdr (assoc-eq nm (cdr (access rewrite-rule rl :heuristic-info))))))

; PETE: I replaced this because in the degenerate case where
;       there is no 'T, then termination does not depend on any variable
;       and if we use nil in the definition rule defunc
;       generates, we get an error.
            ;; (if (member 'T ctrl-pocket)
            ;;     ctrl-pocket
            ;;     nil)
            ctrl-pocket
            )
        nil))))

(include-book "coi/util/pseudo-translate" :dir :system)

(defun c-is-t (c)
  (or (equal c 't) (equal c ''t)))

(defun type-of-pred-aux (pred tbl)
  (cond ((endp tbl) nil)
        ((equal pred (get-alist :predicate (cdar tbl)))
         (caar tbl))
        (t (type-of-pred-aux pred (cdr tbl)))))

#|
(defun type-of-pred (pred tbl)
  (cond ((equal pred 'intp) 'integer)
        ((equal pred 'boolp) 'boolean)
        ((equal pred 'tlp) 'true-list)
        (t (type-of-pred-aux pred tbl))))
|#

(defun type-of-pred (pred tbl ptbl)
  (let ((apred (assoc-equal :type (get-alist pred ptbl))))
    (if apred
        (cdr apred) 
    (type-of-pred-aux pred tbl))))

#|
(type-of-pred 'boolp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'boolp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'bool
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'tlp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'intp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'integerp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred nil
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
|#

(defun enum-of-type (type tbl)
  (get-alist :enumerator (get-alist type tbl)))

; (enum-of-type 'integer (type-metadata-table (w state)))

(defun base-val-of-type (type tbl)
  (get-alist :default-base-value (get-alist type tbl)))

; (base-val-of-type 'integer (type-metadata-table (w state)))

(defun unalias-pred (pred ptbl)
  (let ((apred (assoc-equal :predicate (get-alist pred ptbl))))
    (if apred
        (cdr apred)
      pred)))

(defun pred-of-oc (name formals oc ptbl)
  (and (consp oc) 
       (equal (cdr oc) `((,name ,@formals)))
       (unalias-pred (car oc) ptbl)))

(defun map-force-list (l)
  (if (endp l)
      l
    (cons `(force ,(car l))
          (map-force-list (cdr l)))))

(defun map-force-ic (ic)
  (cond ((equal ic 't) 't)
        ((and (consp ic)
              (equal (car ic) 'acl2::and))
         (cons 'and (map-force-list (cdr ic))))
        (t `(force ,ic))))

(defun wrap-test-skip (skip? x)
  (if skip? `(test-then-skip-proofs ,x) x))

(acl2::program)
(defun add-output-contract-check (body output-contract fun-name fun-args wrld)
  "To body, we insert a runtime check for output-contract."
  (b* (;(ctx 'add-output-contract-check)
       ((mv ?erp tbody) (acl2::pseudo-translate body (list (cons fun-name fun-args)) wrld))
       (vars (all-vars tbody))
       (avoid-lst (union-eq fun-args vars))
       (return-var (acl2::generate-variable '_ret avoid-lst nil nil wrld)))
    `(let ((,return-var ,body))
       (if ,(acl2::subst-expr return-var
                              `(,fun-name ,@fun-args)
                              output-contract)
           ,return-var
         (er hard ',fun-name
             ;; harshrc-- Should we really give an hard
             ;; error here? Perhaps a warning is sufficient, atleast in the
             ;; case where the input-contract was violated in the first place.
             "**Output contract violation**: ~x0 with argument list ~x1 returned ~x2.~%"
             ',fun-name (list ,@fun-args) ,return-var)))))

(defun get-undef-name (pred d? pkg w)
  (declare (xargs :mode :program :guard (symbolp pred)))
  (b* ((tbl (type-metadata-table w))
       (ptbl (pred-alias-table w))
       (type (type-of-pred pred tbl ptbl))
       (undef-name (if type
                       (make-symbl `(acl2s - ,type ,(if d? '-d- '-) undefined) pkg)
                     (if d? 'acl2s::acl2s-d-undefined 'acl2s::acl2s-undefined))))
    (if (acl2::arity undef-name w)
        undef-name
      'acl2s::acl2s-undefined)))

(defun make-defun-body/logic (name formals ic oc body wrld make-staticp d? pkg)
  (b* ((ptbl (pred-alias-table wrld))
       (with-ic-body
        (if (c-is-t ic)
            body
          `(if ,ic
               ,body
             ,(if d?
                  `(,(get-undef-name (pred-of-oc name formals oc ptbl) d? pkg wrld))
                `(,(get-undef-name (pred-of-oc name formals oc ptbl) d? pkg wrld)
                  (quote ,name)
                  (list ,@formals)))))))
    (if make-staticp
        with-ic-body
      (add-output-contract-check with-ic-body oc name formals wrld))))

(defun make-defun-body/exec (name formals oc body wrld make-staticp)
  (if make-staticp
      body
    (add-output-contract-check body oc name formals wrld)))

(defun make-generic-typed-defunc-events
    (name formals ic oc decls body kwd-alist wrld make-staticp d? pkg)
  "Generate events which simulate a typed ACL2s language."
  (b* ((recursivep (get1 :recursivep kwd-alist))
       (force-ic-hyps-in-definitionp 
        (get1 :force-ic-hyps-in-definitionp kwd-alist))
       (skip-admissibilityp 
        (get1 :skip-admissibilityp kwd-alist))
       (ic (if force-ic-hyps-in-definitionp (map-force-ic ic) ic))
       (lbody (make-defun-body/logic name formals ic oc body wrld make-staticp d? pkg))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (fun-ind-name (make-sym name 'induction-scheme-from-definition pkg))
       (ind-scheme-name (make-sym name 'induction-scheme pkg))
       (defun `(defun-no-test ,fun-ind-name ,formals
                 ,@decls
                 ,(subst-fun-sym fun-ind-name name lbody)))
       (defun (wrap-test-skip skip-admissibilityp defun))
       (defthmnotest (if skip-admissibilityp 'defthmskipall 'defthm-no-test))
       (ind-defthm
        `(,defthmnotest ,ind-scheme-name
           t
           :rule-classes ((:induction :pattern ,(cons name formals)
                                      :condition ,ic
                                      :scheme ,(cons fun-ind-name formals)))))
       (def-rule-conc
         `(equal (,name ,@formals) ,ebody))
       (def-rule-body
         (if (equal ic t)
             def-rule-conc
           `(implies ,ic ,def-rule-conc)))
       (def-rule
         `(with-output
           :off :all
           (make-event
            (let ((controller-alist (acl2::controller-alist ',name (w state))))
              `(with-output
                :off :all 
                (,',defthmnotest ,(make-sym ',name 'definition-rule ',pkg)
                  ,',def-rule-body
                  :hints (("Goal" :use ,',name :in-theory nil))
                  :rule-classes ((:definition
                                  ,@(if ,recursivep
                                        `(:controller-alist
                                          ((,',name ,@controller-alist)))
                                      nil))))))))))
    (append

; Submit a function to get an induction scheme?
; Would be good to reuse the termination proof we already did here,
; but the use of ccg make that hard
     (and recursivep
          `(,defun))

     ;; The above defun can take a long time to admit, but
     ;; since its termination argument is exactly the same
     ;; as the main defun, I should investigate how to make
     ;; it go throuh automatically (as we do with many of
     ;; the other forms).

; Induction scheme
     (and recursivep
          `(,ind-defthm))

; Definitional Rule
; Can use skip-proofs here, but this should be fast     
     `(,def-rule)
     ;; The controller-alist argument above is useful when
     ;; we use CCG analysis or an explicit measure. We
     ;; should use whatever controller-alist we used for the
     ;; original function definition.

     ;; Notice also that if defunc does not work with
     ;; mutually recursive definitions. If I wanted it to
     ;; work, I'd have to (in addition to other things), add
     ;; a :clique argument to the above definition rule.

; Disable some rules
     `((in-theory (disable (:definition ,name)
                           ,@(and recursivep
                                  `((:induction ,name)
                                    (:definition ,fun-ind-name))))))
     )))

(logic)

(defun make-contract-body (name ic oc formals d? rem-hyps? f-c-thm? pkg w)
  (declare (xargs :mode :program))
  (b* ((ptbl (pred-alias-table w))
       (pred (pred-of-oc name formals oc ptbl))
       (undef-name (get-undef-name pred d? pkg w)))
    (if (or (c-is-t ic)
            (and rem-hyps?
                 (not (member undef-name '(acl2s::acl2s-undefined
                                           acl2s::acl2s-d-undefined)))))
        (mv oc t)
      (mv `(implies ,(if f-c-thm? (map-force-ic ic) ic) ,oc) nil))))

(defun make-contract-defthm (name ic oc kwd-alist formals d? pkg w)
  (declare (xargs :mode :program))
  (b* ((instructions (get1 :instructions kwd-alist))
       (otf-flg (get1 :otf-flg kwd-alist))
       (hints (get1 :function-contract-hints kwd-alist))
       (rule-classes (get1 :rule-classes kwd-alist))
       (f-c-thm?
        (get1 :force-ic-hyps-in-contract-thmp kwd-alist))
       ((mv body &) (make-contract-body name ic oc formals d? nil f-c-thm? pkg w))
       (skip-function-contractp
        (get1 :skip-function-contractp kwd-alist))
       (defthm
         `(defthm ,(make-sym name 'CONTRACT pkg)
            ,body
            ,@(and hints `(:HINTS ,hints))
            ,@(and rule-classes `(:RULE-CLASSES ,rule-classes))
            ,@(and otf-flg `(:OTF-FLG ,otf-flg))
            ,@(and instructions `(:INSTRUCTIONS ,instructions)))))
    (wrap-test-skip skip-function-contractp defthm)))

(defmacro wrap-skip-fun (x)
  `(wrap-test-skip skip-function-contractp ,x))

(defun make-contract-ev (name formals ic oc kwd-alist make-staticp d? pkg w)
  (declare (xargs :mode :program))
  (b* (((when (c-is-t oc)) nil) ;trivially satisfied
       (function-contract-strictp
        (get1 :function-contract-strictp kwd-alist))
       (f-c-thm?
        (get1 :force-ic-hyps-in-contract-thmp kwd-alist))
       (instructions (get1 :instructions kwd-alist))
       (otf-flg (get1 :otf-flg kwd-alist))
       (hints (get1 :function-contract-hints kwd-alist))
       (rule-classes (get1 :rule-classes kwd-alist))
       (skip-function-contractp
        (get1 :skip-function-contractp kwd-alist))
       ((mv body-rm-hyps no-hyps?-rm-hyps)
        (make-contract-body name ic oc formals d? t f-c-thm? pkg w))
       ((mv body-hyps no-hyps?-hyps)
        (make-contract-body name ic oc formals d? nil f-c-thm? pkg w))
       (contract-name (make-sym name 'CONTRACT pkg))
       (contract-tpname (make-sym name 'CONTRACT-TP pkg))
       (recursivep (get1 :recursivep kwd-alist))
       (ihints `(:hints ;; add induction hint, so user-provided
                 ;; hints are treated as extra
                 ,(append `(("Goal" :induct ,(cons name formals)))
                          hints)))
       (rhints (if recursivep
                   ihints
                 (and hints `(:hints ,hints))))
       (rewrite-class-rm-hyps (if no-hyps?-rm-hyps
                                  '(:rewrite) ;; error if no hyps
                                '(:rewrite :backchain-limit-lst 3)))
       (rewrite-class-hyps (if no-hyps?-hyps
                               '(:rewrite) ;; error if no hyps
                             '(:rewrite :backchain-limit-lst 3)))
       (rclass-rm-hyps
        `(,rewrite-class-rm-hyps
          (:forward-chaining :trigger-terms ((,name ,@formals)))))
       (rclass-hyps
        `(,rewrite-class-hyps
          (:forward-chaining :trigger-terms ((,name ,@formals)))))
       (rclass-rm-hyps (or rule-classes rclass-rm-hyps)) ; rule-classes overrides rclass
       (rclass-hyps (or rule-classes rclass-hyps)) ; rule-classes overrides rclass
       (induct-rewrite-fc
        `(DEFTHM ,contract-name ,body-rm-hyps ,@rhints
           ,@(and rclass-rm-hyps `(:rule-classes ,rclass-rm-hyps))
           ,@(and otf-flg `(:otf-flg ,otf-flg))
           ,@(and instructions `(:instructions ,instructions))))
       (induct-rewrite-fc (wrap-skip-fun induct-rewrite-fc))
       (rewrite-fc ;; in case user wanted to completely override hints
        (and hints
             `(DEFTHM ,contract-name ,body-rm-hyps
                ,@(and hints `(:hints ,hints))
                ,@(and rclass-rm-hyps `(:rule-classes ,rclass-rm-hyps))
                ,@(and otf-flg `(:otf-flg ,otf-flg))
                ,@(and instructions `(:instructions ,instructions)))))
       (rewrite-fc (and rewrite-fc (list (wrap-skip-fun rewrite-fc))))
       (induct-rewrite-fc-h
        `(DEFTHM ,contract-name ,body-hyps ,@rhints
           ,@(and rclass-hyps `(:rule-classes ,rclass-hyps))
           ,@(and otf-flg `(:otf-flg ,otf-flg))
           ,@(and instructions `(:instructions ,instructions))))
       (induct-rewrite-fc-h (wrap-skip-fun induct-rewrite-fc-h))
       (rewrite-fc-h ;; in case user wanted to completely override hints
        (and hints
             `(DEFTHM ,contract-name ,body-hyps
                ,@(and hints `(:hints ,hints))
                ,@(and rclass-hyps `(:rule-classes ,rclass-hyps))
                ,@(and otf-flg `(:otf-flg ,otf-flg))
                ,@(and instructions `(:instructions ,instructions)))))
       (rewrite-fc-h (and rewrite-fc-h (wrap-skip-fun rewrite-fc-h)))
       (rewrite-fc-h (and rewrite-fc-h
                          `((with-output :off :all :on (error)
                                         ,rewrite-fc-h))))
       (induct-rewrite-fc-h
        (if rewrite-fc-h
            `(,induct-rewrite-fc-h)
          `((with-output :off :all :on (error)
                         ,induct-rewrite-fc-h))))
       (tp-rule
        `(DEFTHM ,contract-tpname ,body-rm-hyps
           :rule-classes ((:type-prescription))
           :hints (("goal" :by ,contract-name))))
       (tp-rule (wrap-skip-fun tp-rule))
       (tp-rule-h
        `(DEFTHM ,contract-tpname ,body-hyps
           :rule-classes ((:type-prescription))
           :hints (("goal" :by ,contract-name))))
       (tp-rule-h (wrap-skip-fun tp-rule-h))
       (tp-rule-h
        (and (not (equal tp-rule-h tp-rule))
             `(,tp-rule-h))))
    (cond
     (skip-function-contractp
      `(encapsulate
        ()
        (with-output
         :off :all :on (error)
         ;; ,@induct-rewrite-fc-h)))
         (test-then-skip-proofs ,@induct-rewrite-fc-h))))
     ((or function-contract-strictp make-staticp)
      `(encapsulate
        ()
        (with-output
         :off :all
         (make-event
          '(:or ,induct-rewrite-fc
                ,@rewrite-fc
                ,@induct-rewrite-fc-h
                ,@rewrite-fc-h)))
        (with-output
         :off :all 
         (make-event
          '(:or ,tp-rule
                ,@tp-rule-h
                (value-triple :type-prescription-rule-failed))))))
     (t `(encapsulate
          ()
          (with-output
           :off :all
           (make-event
            '(:OR ,induct-rewrite-fc
                  ,@rewrite-fc
                  ,@induct-rewrite-fc-h
                  ,@rewrite-fc-h
                  (value-triple :function-contract-failed))))
          (with-output
           :off :all
           (make-event
            '(:OR ,tp-rule
                  ,@tp-rule-h
                  (value-triple :Type-prescription-rule-failed)))))))))

#|
(defun make-verify-guards-ev (name kwd-alist)
  (b* ((hints (get1 :body-contracts-hints kwd-alist))
       ;; (get1 :guard-hints xargs{})
       (body-contracts-strictp
        (get1 :body-contracts-strictp kwd-alist))
       (skip-body-contractsp
        (get1 :skip-body-contractsp kwd-alist))
       (hints
        (or hints
            '(("Goal"
               :do-not-induct t
               :do-not '(acl2::generalize acl2::fertilize))))))
    (if (and body-contracts-strictp
             (not skip-body-contractsp))
        `(verify-guards ,name :guard-debug t :hints ,hints)
      `(make-event
        '(:OR (with-output
               :off :all :on (summary error) :summary (time)
               ,(wrap-test-skip
                 skip-body-contractsp
                 `(verify-guards ,name :guard-debug t :hints ,hints)))
              (value-triple :body-contracts-FAILED))))))
|#

(defun make-verify-guards-ev (name kwd-alist)
  (b* ((hints (get1 :body-contracts-hints kwd-alist))
       ;; (get1 :guard-hints xargs{})
       (body-contracts-strictp
        (get1 :body-contracts-strictp kwd-alist))
       (skip-body-contractsp
        (get1 :skip-body-contractsp kwd-alist))
       (hints
        (or hints
            '(("Goal"
               :do-not-induct t
               :do-not '(acl2::generalize acl2::fertilize)))))
       (skip? (or skip-body-contractsp (not body-contracts-strictp))))
    (if skip?
        `(encapsulate
          ()
          (with-output
           :off :all
           (make-event
            '(:OR ,(wrap-test-skip
                    skip-body-contractsp
                    `(verify-guards ,name :guard-debug t :hints ,hints))
                  (value-triple :body-contracts-FAILED)))))
      `(encapsulate
        ()
        (with-output
         :off :all :on (error) 
         (verify-guards ,name :guard-debug t :hints ,hints))))))

; Sometimes counterexample generation winds up trying to evaluate a
; defunc-defined function outside of it's domain.  Now that defunc and
; definec try to prove more general contract theorems, we can get
; contract errors in such cases and that is expected when testing the
; contract theorems.  Such errors can also happen due to things like
; generalization. It useful for debugging to print an error when this
; happens. By default, I turn it off (nil), but it should be on (t)
; when testing defunc.

(encapsulate
  ((acl2s-undefined (x y) t :guard (and (symbolp x) (true-listp y))))
  (local (defun acl2s-undefined (x y) (declare (ignorable x y)) nil)))

(encapsulate
  ((acl2s-d-undefined () t :guard t))
  (local (defun acl2s-d-undefined () nil)))

(defconst *input-contract-alias*
  '(:input-contract :require :assume :pre :pre-condition))

(defconst *output-contract-alias*
  '(:output-contract :ensure :guarantee :post :post-condition))

(defun assoc-equal-alias (alias alist)
  (if (endp alias)
      nil
    (or (assoc-equal (car alias) alist)
        (assoc-equal-alias (cdr alias) alist))))

(defun get1-alias (alias alist)
  (if (endp alias)
      nil
    (or (get1 (car alias) alist)
        (get1-alias (cdr alias) alist))))

(defconst *defunc-keywords*
  (append
   *input-contract-alias*
   *output-contract-alias*
   '(:sig ;:sig unsupported now
     :verbose :debug
     :rule-classes :instructions :function-contract-hints :otf-flg ;for contract defthm
     :body-contracts-hints ;for verify-guards event
     :skip-tests
     :force-ic-hyps-in-definitionp
     :force-ic-hyps-in-contract-thmp
     :skip-admissibilityp
     :skip-function-contractp
     :skip-body-contractsp
     :timeout :termination-strictp :function-contract-strictp :body-contracts-strictp
     )))

(deffilter filter-keywords (xs) keywordp)

(encapsulate
  ((show-contract-violations? () t :guard t))
  (local (defun show-contract-violations? () nil)))

(defun show-contract-violations ()
  (declare (xargs :guard t))
  t)

(defun do-not-show-contract-violations ()
  (declare (xargs :guard t))
  nil)

; PETE:
; If you want to see contract violations printed in an ACL2s
; session, you can do that with the following event:
; (defattach show-contract-violations? show-contract-violations)

(defattach show-contract-violations? do-not-show-contract-violations)

(defun acl2s-undefined-attached (name args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp args))))
  (prog2$ (cgen::cw? (show-contract-violations?)
                     "~|**Input contract violation**: ~x0 ~%"
                     `(,name ,@args))
          nil))

(defattach acl2s-undefined acl2s-undefined-attached)

#|
(defun acl2s-undefined-attached-base (name args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp args))))
  (declare (ignorable name args))
  nil)

; If you want to see contract violations printed in an ACL2s
; session, you can do that with the following event:
; (defattach acl2s-undefined acl2s-undefined-attached-base)

(make-event
 (if *print-contract-violations*
     '(defattach acl2s-undefined acl2s-undefined-attached)
   '(defattach acl2s-undefined acl2s-undefined-attached-base))
 :check-expansion t)

(defun acl2s-d-undefined-attached ()
  (declare (xargs :guard t))
  (prog2$ (cw "~|**Input contract violation** ~%")
          nil))

(defun acl2s-d-undefined-attached-base ()
  (declare (xargs :guard t))
  nil)

(make-event
 (if *print-contract-violations*
     '(defattach acl2s-d-undefined acl2s-d-undefined-attached)
   '(defattach acl2s-d-undefined acl2s-d-undefined-attached-base))
 :check-expansion t)
|#

(defun acl2s-d-undefined-attached ()
  (declare (xargs :guard t))
  (prog2$ (cgen::cw? (show-contract-violations?)
                     "~|**Input contract violation** ~%")
          nil))

(defattach acl2s-d-undefined acl2s-d-undefined-attached)

#!ACL2
(defun modify-xargs-decl (key val decl)
  (b* ((kwd-val-list (cdr (cadr decl)))
       (kwd-val-list (remove-keyword key kwd-val-list)))
    (list 'DECLARE (cons 'XARGS (list* key val kwd-val-list)))))


#!ACL2
(defun update-xargs-decls-fn (decls guard mode)
  "add guard and mode to decls, or create a decl if decls is empty."
  (b* ((xargs-decl (car (last decls)))) ;PRECONDITION: we know that the xargs declare is at the end
    (cond (mode (append (butlast decls 1)
                        (list (modify-xargs-decl :mode mode
                                                 (modify-xargs-decl :guard guard xargs-decl)))))

          (t (append (butlast decls 1)
                     (list (modify-xargs-decl :guard guard xargs-decl)))))))




(defmacro update-xargs-decls (decls &key guard mode)
  `(acl2::update-xargs-decls-fn ,decls ,guard ,mode))
;Note : Macro confusion, if I put ',decls or ',ic, it doesnt
;work. Macros are not that nice, one needs to know the context in
;which they are called, if I call from program context where decls,
;guard are variable names, you should not use quotes, but if you use
;them in a context where decls, guard are actual values, then you need
;to quote them.

(defun print-time-taken (start end state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((- (cw "~|Elapsed Run Time: ")))
    (pprogn (acl2::print-rational-as-decimal (rfix (- end start)) (standard-co state) state)
            (princ$ " seconds" (standard-co state) state)
            (newline (standard-co state) state)
            (value :invisible))))

#|
(defun print-summary-ev (name oc kwd-alist pkg)
  `(with-output :off :all
     (make-event
      (b* ((symbol-class (acl2::symbol-class ',name (w state)))
           (contract-name (make-sym ',name 'contract ',pkg))
           (function-contract-proven-p
            (or (c-is-t ',oc) (acl2::logical-namep contract-name (w state))))
           (print (get1 :print-summary ',kwd-alist))
           ((mv end state) (acl2::read-run-time state))
           ((er &) (if print (print-time-taken ,(get1 :start-time kwd-alist) end state) (value nil)))
           )
          (value
           `(with-output :on :all
              (value-triple
               (cw? ,print
                 "~|Function Name : ~s0 ~|Termination proven -------- [~s1] ~|Function Contract proven -- [~s2] ~|Body Contracts proven ----- [~s3]~%"
                 ',',name
                 (print-*-or-space (not (eq :PROGRAM ,symbol-class)))
                 (print-*-or-space ,function-contract-proven-p)
                 (print-*-or-space (eq :COMMON-LISP-COMPLIANT ,symbol-class))))))))))
|#

#|
(defun print-summary-ev (name oc kwd-alist pkg wrld state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((symbol-class (acl2::symbol-class name wrld))
       (contract-name (make-sym name 'contract pkg))
       (function-contract-proven-p
        (or (c-is-t oc) (acl2::logical-namep contract-name wrld)))
       (print (get1 :print-summary kwd-alist))
       ((mv end state) (acl2::read-run-time state))
       ((er &) (if print
                   (print-time-taken (get1 :start-time kwd-alist) end state)
                 (value nil))))
    (value
     `(value-triple
       (cw? print
         "~|Function Name : ~s0 ~|Termination proven -------- [~s1] ~|Function Contract proven -- [~s2] ~|Body Contracts proven ----- [~s3]~%"
         ',name
         (print-*-or-space (not (eq :PROGRAM ,symbol-class)))
         (print-*-or-space ,function-contract-proven-p)
         (print-*-or-space (eq :COMMON-LISP-COMPLIANT ,symbol-class)))))))
|#

#|


(defun print-summary-ev (name oc kwd-alist pkg)
  `(b* ((symbol-class (acl2::symbol-class ',name (w state)))
        (contract-name (make-sym ',name 'contract ,pkg))
        (function-contract-proven-p
         (or (c-is-t ',oc) (acl2::logical-namep contract-name (w state))))
        (print (get1 :print-summary ',kwd-alist)))
     (value
      `(value-triple
        (cw? ,print
          "~|Function Name : ~s0 ~|Termination proven -------- [~s1] ~|Function Contract proven -- [~s2] ~|Body Contracts proven ----- [~s3]~%"
          ',',name
          (print-*-or-space (not (eq :PROGRAM ,symbol-class)))
          (print-*-or-space ,function-contract-proven-p)
          (print-*-or-space (eq :COMMON-LISP-COMPLIANT ,symbol-class)))))))

|#


(defun print-summary-ev (name oc kwd-alist pkg)
  `(b* ((symbol-class (acl2::symbol-class ',name (w state)))
        (contract-name (make-sym ',name 'contract ,pkg))
        (function-contract-proven-p
         (or (c-is-t ',oc) (acl2::logical-namep contract-name (w state))))
        (print (get1 :print-summary ',kwd-alist))
        ((mv end state) (acl2::read-run-time state))
        ((er &) (if print
                    (print-time-taken ,(get1 :start-time kwd-alist)
                                      end state)
                  (value nil))))
     (value
      `(value-triple
        (cw? ,print
          "~|Function Name : ~s0 ~|Termination proven -------- [~s1] ~|Function Contract proven -- [~s2] ~|Body Contracts proven ----- [~s3]~%"
          ',',name
          (print-*-or-space (not (eq :PROGRAM ,symbol-class)))
          (print-*-or-space ,function-contract-proven-p)
          (print-*-or-space (eq :COMMON-LISP-COMPLIANT ,symbol-class)))))))

(defun print-*-or-space (b)
  (if b "*" " "))

(defmacro me-assign (var val) ; make-event-assign
  `(make-event (er-progn (assign ,var ,val)
                         (value '(value-triple :invisible)))))

(defun make-defun-no-guard-ev
    (name formals ic oc decls body kwd-alist wrld make-staticp d? pkg)
  (declare (xargs :mode :program))
  (b* ((lbody (make-defun-body/logic name formals ic oc body wrld make-staticp d? pkg))
       (ebody (make-defun-body/exec name formals oc body wrld make-staticp))
       (skip-admissibilityp 
        (get1 :skip-admissibilityp kwd-alist))
       (termination-strictp
        (get1 :termination-strictp kwd-alist))
       (decls (update-xargs-decls decls :guard ic))
       (defun (list* 'acl2::defun name formals
                     (append decls
                             (list (list 'acl2::mbe :logic lbody :exec
                                         ebody))))))
    (cond (skip-admissibilityp
           `(encapsulate
             ()
             (with-output
              :off :all :on (error) 
              (skip-proofs ,defun))))
          (termination-strictp
           `(encapsulate
             ()
             (with-output
              :off :all :on (error)
              ,defun)))
          (t `(encapsulate
               ()
               (with-output
                :off :all
                (encapsulate
                 ()
                 (local (me-assign acl2::ccg-inhibit-output-lst
                                   *ccg-valid-output-names*))
                 (make-event
                  '(:OR ,defun
                        (acl2::fail-event
                         :termination t
                         :fail "Termination Proof Failed"))))))))))

(defun timeout-abort-fn (start-time timeout-secs debug state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((mv end state) (acl2::read-run-time state))
       (time-elapsed (- end start-time))
       (- (cw? debug  "~| Elapsed Time is ~x0 and timeout-secs is ~x1 ~%" time-elapsed timeout-secs))
       (- (cw? (> time-elapsed timeout-secs) "~|Defunc timeout exceeded!!~%")))
    (if (> time-elapsed timeout-secs)
        (mv t nil state)
      (value '(value-triple :invisible)))))


(defmacro abort-this-event-sequence (start-time timeout-secs debug)
  "If timedout or reason was termiantion -- just raise error"
  `(with-output :off :all
     (make-event (er-progn
                  (if (and (acl2::boundp-global 'defunc-failure-reason state)
                           (eq (@ defunc-failure-reason) :termination))
                      (mv t nil state)
                    (value nil))
                  (assign defunc-failure-reason :timed-out)
                  (timeout-abort-fn ,start-time ,timeout-secs ,debug state)))))

(defun defunc-events-with-staticp-flag
    (name formals ic oc decls body kwd-alist wrld make-staticp d? pkg)
  "Depending on flag make-staticp, we generate either events with static contract or with dynamic contract (run-time checking)."
  (declare (xargs :mode :program))
  (if (get1 :program-mode-p kwd-alist)
      '(mv t nil state) ;skip/abort
    (b* ((defun/ng
           (make-defun-no-guard-ev
            name formals ic oc decls body kwd-alist wrld make-staticp d? pkg))
         (contract-defthm
          (make-contract-ev name formals ic oc kwd-alist make-staticp d? pkg wrld))
         (contract-defthm
          (or contract-defthm
              '(encapsulate
                ()
                (value-triple :trivial-contract-thm))))
         (verify-guards-ev (make-verify-guards-ev name kwd-alist))
         (timeout-secs (get1 :timeout kwd-alist))
         ;; PETE: make sure this makes sense
         ;; We already tested the defunc, so why do it again?
         (test-subgoals-p nil))
;         (test-subgoals-p (eq t (get1 :testing-enabled kwd-alist))))
      `(with-output
        :off :all
        (with-time-limit
         ,timeout-secs
         (encapsulate
          nil
          ,@(and test-subgoals-p
                 '((local (acl2s-defaults :set testing-enabled nil))))
          (local (acl2s-defaults :set print-cgen-summary nil))
          (me-assign defunc-failure-reason :termination)
          
          ;;(with-time-limit ,timeout-secs ,defun/ng)
          (value-triple
           (cw "~|Form:  ( ADMIT-DEFINITION ~x0 ... )~%" ',name))

          (with-output
           :off :all :on (summary) :summary (time) 
;           :off :all :on (error summary) :summary (time) 
           (with-time-limit ,(* 4/5 timeout-secs) ,defun/ng))

          (me-assign defunc-failure-reason :contract)

;         ,@(and test-subgoals-p
;                '((local (acl2s-defaults :set testing-enabled t))))
          ;;helps defeat generalizations
          (value-triple
           (cw "~|Form:  ( PROVE-FUNCTION-CONTRACT ~x0 ... )~%" ',name))
          ,@(and contract-defthm ;(list contract-defthm))
                 `((with-output
;                    :off :all :on (summary error) :summary (time)
                    :off :all :on (summary) :summary (time)
                    (with-time-limit ,(* 1/3 timeout-secs) ,contract-defthm))))
;         ,@(and test-subgoals-p
;                '((local (acl2s-defaults :set testing-enabled nil))))
          (me-assign defunc-failure-reason :guards)

          (value-triple
           (cw "~|Form:  ( PROVE-BODY-CONTRACTS ~x0 ... )~%" ',name))
         
          (with-output
           :off :all :on (summary) :summary (time)
           (with-time-limit
            ,(* 1/3 timeout-secs) ,verify-guards-ev))
         
          (me-assign defunc-failure-reason :generic-ev)
          
          ,@(make-generic-typed-defunc-events
             name formals ic oc decls body kwd-alist wrld make-staticp d? pkg)
          
          (me-assign defunc-failure-reason :none)

          (make-event
           ,(print-summary-ev name oc kwd-alist pkg))))))))

#|
(defun program-mode-defunc-events (name formals ic oc decls body kwd-alist d? wrld pkg)
  (declare (xargs :mode :program))
  (b* ((dynamic-body (make-defun-body/logic name formals ic oc body wrld nil d? pkg))
       (decls (update-xargs-decls decls :guard ic :mode :program)))
    `(with-output
       :on (error summary) :summary (form)
       (PROGN
        (defun ,name ,formals
          ,@decls
          ,dynamic-body)
        ,(print-summary-ev name oc kwd-alist pkg)))))
|#

(defun program-mode-defunc-events
    (name formals ic oc decls body kwd-alist d? wrld pkg)
  (declare (xargs :mode :program))
  (b* ((dynamic-body (make-defun-body/logic name formals ic oc body wrld nil d? pkg))
       (decls (update-xargs-decls decls :guard ic :mode :program))
       (timeout-secs (get1 :timeout kwd-alist)))
    `(with-output
      :off :all
      (with-time-limit
       ,timeout-secs
       (encapsulate
        nil
        (local (acl2s-defaults :set testing-enabled t))
        (local (acl2s-defaults :set print-cgen-summary nil))
        (me-assign defunc-failure-reason :termination)
        (value-triple
         (cw "~|Form:  ( ADMIT-DEFINITION ~x0 ... )~%" ',name))
        (with-output
         :off :all :on (error summary) :summary (time) 
         (defun ,name ,formals
           ,@decls
           ,dynamic-body))
        (me-assign defunc-failure-reason :none)
        (make-event ,(print-summary-ev name oc kwd-alist pkg)))))))

(defun print-guard-extra-info-hyps (hyps yesp)
  (if (endp hyps)
      nil
    (if (and (consp (car hyps))
             (eq (car (car hyps)) 'ACL2::EXTRA-INFO))
        (prog2$
         (cgen::cw? yesp "~| -- ~x0~%" (car hyps))
         (print-guard-extra-info-hyps (cdr hyps) yesp))
      (print-guard-extra-info-hyps (cdr hyps) yesp))))

;; ((acl2::fun (check-syntax form logicp state)) ;flet
;;          (acl2::state-global-let*
;;           ((acl2::inhibit-output-lst acl2::*valid-output-names*))
;;           (acl2::translate form T logicp T "test-guards" (w state) state)))

(defun test-guards1 (guards hints override-defaults timeout state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp guards)
      (value nil)
    (b* (((mv erp & state)
          ;; test?-fn will use a timeout and if there is a timeout, erp=nil
          (with-time-limit
           timeout
           (test?-fn (car guards) hints override-defaults state)))
         (vl  (acl2s-defaults :get verbosity-level))
         (show-falsified-guards-p (and erp (cgen::normal-output-flag vl)))
         ;; If there is a timeout, then show-falsified-guards-p=nil,
         ;; so don't do potentially expensive simplification work.
         ((unless show-falsified-guards-p) (value nil))

         (- (cgen::cw? show-falsified-guards-p "~|Body contract falsified in: ~%"))

; [2015-02-04 Wed] Add extra support to blame the falsified body contract by looking through lambda/let/assumptions/etc

         ((mv & gterm state) (cgen::check-syntax (car guards) NIL state))
         ((mv hyps concl state) (cgen::partition-hyps-concl gterm "test-guards" state))
; This takes a long time sometimes, so quit before getting here with
; unless checke above, but may also want to remove this simplification
; and instead add a keyword setting. the code for removing it is
; commented out below. 
         ((mv & nconcl state) (cgen::simplify-term (list 'not concl) hyps nil state))
;         (nconcl (list 'not concl))
         (hyps1 (acl2::expand-assumptions-1 nconcl))

         (- (print-guard-extra-info-hyps (append hyps hyps1) show-falsified-guards-p))
         ((when erp) (mv t nil state)))
      (test-guards1 (cdr guards) hints override-defaults timeout state))))


(defun test-guards (guard-obligation hints override-defaults timeout state)
  "This is just a looping test?-fn over multiple guards, and on error, printing out the appropriate guard-info."
  (declare (xargs :mode :program :stobjs (state)))
  (b* ((guards (if (and (consp guard-obligation)
                        (eq 'ACL2::AND (car guard-obligation)))
                   (cdr guard-obligation)
                 (list guard-obligation))))
    (test-guards1 guards hints override-defaults timeout state)))

;; If ld-error-action is :error, ld stops and returns, signalling an
;; error to its caller by returning an error triple with non-nil error
;; component, and reverting the logical world to its value just before
;; that call of ld.

(defun test?-phase (parsed state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (skip-tests-p (or (get1 :skip-tests kwd-alist)
                         (eq nil (get1 :testing-enabled kwd-alist))))
       (testing-timeout (get1 :cgen-timeout kwd-alist))
       ((when skip-tests-p) (value nil))
       (mode (if (get1 :program-mode-p kwd-alist) :program :logic))
       (defun (list* 'ACL2::DEFUN name formals
                     (append (update-xargs-decls decls :guard ic :mode mode)
                             (list body))))
       (redef? (and (getpropc name 'formals) t))
       (debug (get1 :debug kwd-alist))
       (- (cw? debug "~|defun : ~x0 ~| ic : ~x1 ~| oc: ~x2~%" defun ic oc))
       (hints (get1 :body-contracts-hints kwd-alist))
       ((mv start state) (acl2::read-run-time state))
       (- (cw "~%~|Form:  ( TEST-DEFINITION ~x0 ... )~%" name))
       ((er trval)
        (with-output!
         :off :all ;:on (summary) :summary (time)
         (acl2::trans-eval
          `(make-event
            (with-output 
             :off :all ;:on (error)
             ;; Pete: Below, we have to check for redefinitions. If
             ;; the current defunc is a redefinition that just has
             ;; different keywords, say :skip-tests t in one version,
             ;; but not the other, then we would get an error here
             ;; with the skip-proofs form. We can avoid it by using
             ;; :skip-tests t in the defunc, but it seems best to not
             ;; require that. So, now I check to see if the function
             ;; is defined, and if so, I do not try to define it
             ;; again. If this is problematic, say because the
             ;; definitions are different, we'll figure it out during
             ;; the admission process. I thought about defining defun
             ;; above so that it matches what defunc-events would do,
             ;; but I can't do that since defunc-events may generate a
             ;; program mode function and I won't be able to figure
             ;; that out without running it.
             (b* (((er &)
                   (if ,redef?
                       (value '(value-triple :invisible))
                     (with-output! :off :all :on (error) (skip-proofs ,defun))))
                  (- (cw "~|Form:  ( TEST-BODY-CONTRACTS ~x0... ) ~%" ',name))
                  ((er guard-ob) (acl2::function-guard-obligation ',name state))
                  (- (cw? ,debug "~|Guard obligation: ~x0~%" guard-ob))
                  ((er &) (with-time-limit
                           ,testing-timeout
                           (with-output!
                            :off :all :on (error)
                            (test-guards guard-ob
                                         ',hints
                                         '(:print-cgen-summary nil :num-witnesses 0)
                                         ,testing-timeout
                                         state))))
                  (- (cw "~|Form:  ( TEST-FUNCTION-CONTRACT ~x0 ...) ~%" ',name))
                  ((er &) (with-time-limit
                           ,testing-timeout
                           (with-output!
                            :off :all :on (error)
                            (test? (implies ,ic ,oc)
                              :print-cgen-summary nil
                              :num-witnesses 0))))
                  (- (cw "~|Testing: Done ~%")))
               (value '(value-triple :invisible)))))
          'test?-phase state t)))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       ((mv end state) (acl2::read-run-time state))
       ((er &) (print-time-taken start end state))
       )
    (value nil)))


#|

(defun test?-phase (parsed state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (skip-tests-p (or (get1 :skip-tests kwd-alist)
                         (eq nil (get1 :testing-enabled kwd-alist))))
       (testing-timeout (get1 :cgen-timeout kwd-alist))
       ((when skip-tests-p) (value nil))
       (mode (if (get1 :program-mode-p kwd-alist) :program :logic))
       (defun (list* 'ACL2::DEFUN name formals
                     (append (update-xargs-decls decls :guard ic :mode mode)
                             (list body))))
       (debug (get1 :debug kwd-alist))
       (- (cw? debug "~| defun : ~x0 ~| ic : ~x1 ~| oc: ~x2~%" defun ic oc))
       (hints (get1 :body-contracts-hints kwd-alist))
       ((mv start state) (acl2::read-run-time state))
       (- (cw "~|Testing: Defining function ... ~%"))
       ((er trval)
        (acl2::trans-eval
         `(make-event
           (er-progn
            (with-output
             :on (error summary event)
             (skip-proofs ,defun))
            (value '(value-triple :done-def))))
         'test?-phase state t))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       (- (cw "~|Query: Defining function for testing ... ~%"))
       ((er trval)
        (with-output!
         :on (error summary) :summary (acl2::value)
         (acl2::trans-eval
          `(make-event
            (with-output 
             :on (error)
            (b* ((- (cw "~|Testing: Defining function ... ~%"))
                 ((er &)
                  (skip-proofs ,defun)))
              (value '(value-triple :invisible)))))
          'test?-phase state t))
        )
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       (- (cw "~|Query: Testing body contracts ... ~%"))
       ((er trval)
        (acl2::trans-eval
         `(make-event
           (with-output 
            :on (error)
            (b* (((er guard-ob) (acl2::function-guard-obligation ',name state))
                 (- (cw? ,debug "~|Guard obligation: ~x0~%" guard-ob))
                 ((er &) (with-output
                          :on (error)
                          (with-time-limit
                           ,testing-timeout
                           (test-guards guard-ob
                                        ',hints
                                        '(:print-cgen-summary nil :num-witnesses 0)
                                        ,testing-timeout
                                        state)))))
              (value '(value-triple :invisible)))))
         'test?-phase state t))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       (- (cw "~|Query: Testing function contract ... ~%"))
       ((er trval)
        (acl2::trans-eval
         `(make-event
           (er-progn
            (with-output
             :on (error)
             (skip-proofs ,defun))
            (with-output
             :on (error)
             (with-time-limit
              ,testing-timeout
              (test? (implies ,ic ,oc) :print-cgen-summary nil :num-witnesses 0)))
            (value '(value-triple :invisible))))
         'test?-phase state t))
       ((when (eq T (cadr trval))) (mv t nil state)) ;abort with error
       ((mv end state) (acl2::read-run-time state))
       ((er &) (print-time-taken start end state))
       )
    (value nil)))

|#

;       (- (cw "~| ld erp: ~x0 defun-name logical-namep result: ~x1 ld-err-triple: ~x2~%" erp (logical-namep name (w state)) (ld-error-triples state))))
;; ;; THis is stupid. ACL2 should have a error-propagating mechanism where errors have names!!
;;     (if (eq :passed (@ _test?-phase__ld-result))
;;         (mv t :passed state)
;;       (mv t nil state))))

(defun make-show-failure-msg-ev (start-time kwd-alist events-seen)
  `(with-output
    :off :all :on (error)
    (make-event
     (b* ((body-contracts-strictp (get1 :body-contracts-strictp ',kwd-alist))
          (function-contract-strictp (get1 :function-contract-strictp ',kwd-alist))
          (termination-strictp (get1 :termination-strictp ',kwd-alist))
          (timeout-secs (get1 :timeout ',kwd-alist))
          ((mv end state) (acl2::read-run-time state))
          ((er &) (print-time-taken ,start-time end state))
          (time-elapsed (- end ,start-time))
          (failure-reason (@ defunc-failure-reason))
          (blame-msg
           (or (and (or (> time-elapsed timeout-secs) (eq :timed-out failure-reason))
                    "Defunc has TIMED OUT!! You can change the timeout default using :timeout option (also see :doc set-defunc-timeout). If you want to bypass this failure, you can modify defunc's default strictness (see :doc defunc).")
               (and termination-strictp (eq :termination failure-reason)
                    "Termination FAILED!")
               (and function-contract-strictp (eq :contract failure-reason)
                    "Function Contract FAILED! You can provide :function-contract-hints to help.")
               (and body-contracts-strictp (eq :guards failure-reason)
                    "Body Contracts FAILED! You can provide :body-contracts-hints to help.")
               "Something that we could not assign blame to has FAILED! The failure might be due to the definition rule or the induction scheme associated with this function definition. Chances are that there is a problem with your definition. To debug this further, please consult an expert."))
          )

       (if (> time-elapsed timeout-secs)
           (value
            `(with-output
              :off :all :on (error)
              (value-triple (er hard? 'defunc "~%~s0~%" ,blame-msg))))
         (value
          `(with-output
            :off :all :on (error)
            (value-triple
             (progn$
              (fmt-to-comment-window
               "~%~%FAILED EVENTS: ~x0"
               (list (cons #\0 (list* 'ACL2::PROGN ',',events-seen))) 0 nil nil)
              (cw "~%~s0" ,blame-msg)
              (er hard? 'defunc
                  "~|Submit the events shown above to replicate the failure."))))))))))

(defun events-seen-list (parsed wrld make-staticp d? pkg)
  (declare (xargs :mode :program))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (defun/ng
         (make-defun-no-guard-ev name formals ic oc decls body
                                 kwd-alist wrld make-staticp d? pkg))
       (contract-defthm (make-contract-defthm name ic oc kwd-alist formals d? pkg wrld))
       (verify-guards-ev (make-verify-guards-ev name kwd-alist))
       (function-contract-strictp (get1 :function-contract-strictp kwd-alist))
       (body-contracts-strictp (get1 :body-contracts-strictp kwd-alist)))
    (append (list defun/ng)
            (and function-contract-strictp contract-defthm (list contract-defthm))
            (and body-contracts-strictp (list verify-guards-ev)))))


(deffilter filter-xargs-decls (decls)
  (lambda (x) (and (= 2 (len x))
                   (consp (cadr x))
                   (eq 'ACL2::XARGS (car (cadr x))))))


(defun union-keyword-value-lists (kwd-val-lst1 kwd-val-lst2)
  (if (endp kwd-val-lst1)
      kwd-val-lst2
    (b* ((key (car kwd-val-lst1))
         (value (cadr kwd-val-lst1))
         (rest (cddr kwd-val-lst1)))
      (union-keyword-value-lists
       rest
       (list* key value (acl2::remove-keyword key kwd-val-lst2))))))

#!ACL2
(defun collect-xargs-into-single-declare (xargs-decls ans-kwd-val-lst)
  (if (endp xargs-decls)
      (list
       'DECLARE
       (cons
        'XARGS
        (list* :VERIFY-GUARDS NIL
               :NORMALIZE NIL ;o.w definition-rule fails in e.g defunc len
               (remove-keyword :normalize
                               (remove-keyword :verify-guards ans-kwd-val-lst)))))
    (b* ((curr-kwd-val-lst (cdr (cadr (car xargs-decls)))))

      (collect-xargs-into-single-declare
       (cdr xargs-decls)
       (acl2s::union-keyword-value-lists curr-kwd-val-lst ans-kwd-val-lst)))))

(defun squeeze-multiple-xarg-decls (decls)
  "collect all xargs decls, squeeze them into one decl and put that at the end."
  (b* ((xargs-decls (filter-xargs-decls decls))
       (xargs-decl (acl2::collect-xargs-into-single-declare xargs-decls '())))
    (append (set-difference-equal decls xargs-decls) (list xargs-decl))))

(deffilter filter-strings (xs) stringp)

(table defunc-defaults-table nil
       '((:debug       .  nil)
         (:verbose     . nil)
         (:print-summary  . t)
         (:skip-tests . nil)
         (:timeout . 50)
         (:termination-strictp . t)
         (:function-contract-strictp . t)
         (:body-contracts-strictp . t)
         (:force-ic-hyps-in-contract-thmp . t)
         (:force-ic-hyps-in-definitionp . nil)
         (:skip-admissibilityp . nil)
         (:skip-function-contractp . nil)
         (:skip-body-contractsp . nil)
         )
       :clear)

(verify-termination remove1-assoc-eq-lst)

;; (defmacro termination-strictp () `(cdr (assoc-eq :termination-strictp (table-alist 'defunc-defaults-table wrld))))
;; (defmacro function-contract-strictp () `(cdr (assoc-eq :function-contract-strictp (table-alist 'defunc-defaults-table wrld))))
;; (defmacro body-contracts-strictp () `(cdr (assoc-eq :body-contracts-strictp (table-alist 'defunc-defaults-table wrld))))

(defun defunc-table (wrld)
  "api to get the alist representing defun-defaults-table"
  (declare (xargs :guard (plist-worldp wrld)))
  (table-alist 'defunc-defaults-table wrld))


(defloop thereis-programp (fns wrld)
  (for ((fn in fns)) (thereis (acl2::programp fn wrld))))

(defun program-mode-p (name formals body decls wrld)
  "Check if :mode :program is declared, or check if current mode is (program), or if body has a program-mode function call"
  (declare (xargs :mode :program))
  (b* ((xargs{} (xargs-kwd-alist decls 'program-mode-p))
       (pm? (eq (get1 :mode xargs{}) :program))
       ((mv ?erp tbody) (acl2::pseudo-translate body (list (cons name formals)) wrld))
       (sub-fns (set-difference-eq (cgen::all-functions tbody) (list name))))
    (or pm?
        (eq (cdr (assoc-eq :defun-mode (table-alist 'acl2::acl2-defaults-table wrld)))
            :program)
        (thereis-programp sub-fns wrld))))
#|

(defun type-of-type (type tbl atbl ctx)
  (let ((atype (assoc-equal :type (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist type tbl)))
        (if res
            type
          (er soft ctx
 "~%**Unknown type **: ~x0 is not a known type name.~%" type ))))))

(defun pred-of-type (type tbl atbl ctx)
  (let ((atype (assoc-equal :predicate (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist :predicate (get-alist type tbl))))
        (or res
            (er hard ctx
 "~%**Unknown type **: ~x0 is not a known type name.~%" type ))))))

|#

; Decided to take care of error printing on my own, but kept previous
; versions above.
(defun type-of-type (type tbl atbl ctx)
  (declare (ignore ctx))
  (let ((atype (assoc-equal :type (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist type tbl)))
        (if res
            type
          nil)))))

(defun pred-of-type (type tbl atbl ctx)
  (declare (ignore ctx))
  (let ((atype (assoc-equal :predicate (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist :predicate (get-alist type tbl))))
        res))))

(defun make-output-contract (name args type)
  (cond ((equal type 'acl2s::allp) t)
        (t `(,type ,(cons name args)))))

(defun parse-defunc (name args pkg wrld)
  ;; Returns (list nm formals ic oc doc decls body kwd-alist)
  (declare (xargs :mode :program))
  (declare (ignorable wrld))
  (b* ((ctx 'defunc)
       ((unless (or (legal-variablep name)
                    (and (symbolp name) (equal "*" (symbol-name name))))) ;exception
        (er hard? ctx "~| Function name ~x0 expected to be a legal variable.~%" name))

       (defaults-alst (table-alist 'defunc-defaults-table wrld))
       (defaults-alst (remove1-assoc-eq-lst (filter-keywords args) defaults-alst))
       (defaults-alst (put-assoc :testing-enabled (get-acl2s-defaults 'testing-enabled wrld) defaults-alst))
       (defaults-alst (put-assoc :cgen-timeout (get-acl2s-defaults 'cgen-timeout wrld) defaults-alst))
       ((mv kwd-alist defun-rest) (extract-keywords ctx *defunc-keywords* args defaults-alst))
       (tbl (table-alist 'type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
          
       (formals (car defun-rest))
       (decls/docs (butlast (cdr defun-rest) 1))
       (body  (car (last defun-rest)))
       (full-input-contract (assoc-equal-alias *input-contract-alias* kwd-alist))
       (full-output-contract (assoc-equal-alias *output-contract-alias* kwd-alist))

       ((unless full-input-contract)
        (er hard ctx "~|Defunc is missing an input contract. ~%" ))
       ((unless full-output-contract)
        (er hard ctx "~|Defunc is missing an output contract. ~%" ))

       (input-contract (get1-alias *input-contract-alias* kwd-alist ))
       (output-contract (get1-alias *output-contract-alias* kwd-alist ))
       (kword-oc? (keywordp output-contract))
       (f-type (and kword-oc? (intern$ (symbol-name output-contract) pkg)))
       (f-type-pred (and kword-oc? (pred-of-type f-type tbl atbl 'defunc)))
       (output-contract
        (if kword-oc?
            (make-output-contract name formals f-type-pred)
          output-contract))

       ((unless (simple-termp input-contract))
        (er hard ctx "~|The input contract has to be a term. ~x0 is not.~%" input-contract))
       ((unless (simple-termp output-contract))
        (er hard ctx "~|The output contract has to be a term. ~x0 is not.~%" output-contract))
;       (signature (get1 :sig kwd-alist))

       ((mv ?erp p-body)
        (acl2::pseudo-translate body (list (cons name formals)) wrld))
       (recp (and (member-equal name (acl2::all-fnnames p-body)) t))
       (kwd-alist (put-assoc :recursivep recp kwd-alist))

       (docs (filter-strings decls/docs))
       ((when (consp (cdr docs)))
        (er hard ctx "~|Multiple doc strings unexpected!~%" docs))
       (doc-strings (and (consp docs) (list (car docs))))
       (decls (set-difference-equal decls/docs docs))
       (decls (squeeze-multiple-xarg-decls decls))
       (decls (append doc-strings decls)) ;put doc-string at the front of decls

       (program-mode-p (program-mode-p name formals body decls wrld))
       (kwd-alist (put-assoc :program-mode-p program-mode-p kwd-alist))
       )

    (list name formals input-contract output-contract decls body kwd-alist)))

(defun make-undefined-aux (parsed w d? do-it pkg)
  (declare (xargs :mode :program))
  (b* (((list name formals & oc & & kwd-alist) parsed)
       (tbl (type-metadata-table w))
       (ptbl (pred-alias-table w))
       (skip-admissibilityp 
        (get1 :skip-admissibilityp kwd-alist))
       (pred (pred-of-oc name formals oc ptbl))
       (type (type-of-pred pred tbl ptbl))
       (undef-name (if type
                       (make-symbl `(acl2s - ,type ,(if d? '-d- '-) undefined) pkg)
                     (if d? 'acl2s::acl2s-d-undefined 'acl2s::acl2s-undefined)))
       (attch-name (make-symbl `(,undef-name ,(if d? '-d- '-) attached) pkg))
       (thm-name (make-symbl `(,undef-name ,(if d? '-d- '-) ,pred) pkg))
       (base-val (and type (base-val-of-type type tbl)))
       (defthm-d? `(defthm ,thm-name (,pred (,undef-name))
                     :rule-classes ((:type-prescription) (:rewrite))))
       (defthm-d? (if skip-admissibilityp
                      `(test-then-skip-proofs ,defthm-d?)
                    defthm-d?))
       (defthm-no-d? `(defthm ,thm-name (,pred (,undef-name x y))
                        :rule-classes ((:type-prescription) (:rewrite))))
       (defthm-no-d? (if skip-admissibilityp
                         `(test-then-skip-proofs ,defthm-no-d?)
                       defthm-no-d?))
       (def-att `(defattach ,undef-name ,attch-name))
       (def-att (if skip-admissibilityp
                    `(test-then-skip-proofs ,def-att)
                  def-att))
       (d?-form `(encapsulate
                  nil
                  (encapsulate
                   ((,undef-name () t))
                   (local (defun ,undef-name ()
                            ',base-val))
                   ,defthm-d?)
                  (defun ,attch-name ()
                    (declare (xargs :guard t))
                    (prog2$ (cgen::cw?
                             (show-contract-violations?)
                             "~|**Input contract violation in ~x0** ~%"
                             ',attch-name)
                            ',base-val))
                  ,def-att))
       (no-d?-form `(encapsulate
                     nil
                     (encapsulate
                      ((,undef-name (x y) t :guard (and (symbolp x) (true-listp y))))
                      (local (defun ,undef-name (x y)
                               (declare (ignorable x y))
                               ',base-val))
                      ,defthm-no-d?)
                     (defun ,attch-name (x y)
                       (declare (xargs :guard (and (symbolp x) (true-listp y))))
                       (prog2$ (cgen::cw?
                                (show-contract-violations?)
                                "~|**Input contract  violation in ~x0**: ~x1 ~%"
                                ',attch-name `(,x ,@y))
                               ',base-val))
                     ,def-att)))
    (cond
     ((and (not do-it)
           (get1 :program-mode-p kwd-alist))
      `(value-triple :program-mode))
     ((and (not do-it)
           (acl2::arity undef-name w))
      `(value-triple ',undef-name))
     (d? d?-form)
     (t no-d?-form))))

#|
(defun make-undefined-aux (parsed w d? do-it pkg)
  (declare (xargs :mode :program))
  (b* (((list name formals & oc & & kwd-alist) parsed)
       (tbl (type-metadata-table w))
       (ptbl (pred-alias-table w))
       (skip-admissibilityp 
        (get1 :skip-admissibilityp kwd-alist))
       (pred (pred-of-oc name formals oc ptbl))
       (type (type-of-pred pred tbl ptbl))
       (undef-name (if type
                       (make-symbl `(acl2s - ,type ,(if d? '-d- '-) undefined) pkg)
                     (if d? 'acl2s::acl2s-d-undefined 'acl2s::acl2s-undefined)))
       (attch-name (make-symbl `(,undef-name ,(if d? '-d- '-) attached) pkg))
       (attch-base-name (make-symbl `(,attch-name ,(if d? '-d- '-) base) pkg))
       (thm-name (make-symbl `(,undef-name ,(if d? '-d- '-) ,pred) pkg))
       (base-val (and type (base-val-of-type type tbl)))
       (defthm-d? `(defthm ,thm-name (,pred (,undef-name))
                     :rule-classes ((:type-prescription) (:rewrite))))
       (defthm-d? (if skip-admissibilityp
                      `(test-then-skip-proofs ,defthm-d?)
                    defthm-d?))
       (defthm-no-d? `(defthm ,thm-name (,pred (,undef-name x y))
                        :rule-classes ((:type-prescription) (:rewrite))))
       (defthm-no-d? (if skip-admissibilityp
                         `(test-then-skip-proofs ,defthm-no-d?)
                       defthm-no-d?))
       (def-att (if *print-contract-violations*
                    `(defattach ,undef-name ,attch-name)
                  `(defattach ,undef-name ,attch-base-name)))
       (def-att (if skip-admissibilityp
                    `(test-then-skip-proofs ,def-att)
                  def-att))
       (d?-form `(encapsulate
                  nil
                  (encapsulate
                   ((,undef-name () t))
                   (local (defun ,undef-name ()
                            ',base-val))
                   ,defthm-d?)
                  (defun ,attch-name ()
                    (declare (xargs :guard t))
                    (prog2$ (cw "~|**Input contract violation** ~%")
                            ',base-val))
                  (defun ,attch-base-name ()
                    (declare (xargs :guard t))
                    ',base-val)
                  ,def-att))
       (no-d?-form `(encapsulate
                     nil
                     (encapsulate
                      ((,undef-name (x y) t :guard (and (symbolp x) (true-listp y))))
                      (local (defun ,undef-name (x y)
                               (declare (ignorable x y))
                               ',base-val))
                      ,defthm-no-d?)
                     (defun ,attch-name (x y)
                       (declare (xargs :guard (and (symbolp x) (true-listp y))))
                       (prog2$ (cw "~|**Input contract violation**: ~x0 ~%" `(,x ,@y))
                               ',base-val))
                     (defun ,attch-base-name (x y)
                       (declare (xargs :guard (and (symbolp x) (true-listp y))))
                       (declare (ignorable x y))
                       ',base-val)
                     ,def-att)))
    (cond
     ((and (not do-it)
           (get1 :program-mode-p kwd-alist))
      `(value-triple :program-mode))
     ((and (not do-it)
           (acl2::arity undef-name w))
      `(value-triple ',undef-name))
     (d? d?-form)
     (t no-d?-form))))
|#

(defun make-undefined (name args d? pkg w)
  (declare (xargs :mode :program :guard (symbolp name)))
  (make-undefined-aux (parse-defunc name args pkg w) w d? nil pkg))

; (make-event (make-undefined 'foo '((x) :input-contract (natp x) :output-contract (booleanp (foo x)) nil)  (w state)))
; (make-event (make-undefined 'booleanp (w state)))
; (make-event (make-undefined 'boole (w state)))

(defun defunc-events (parsed d? state)
  (declare (xargs :mode :program :stobjs (state)))
  (b* (((list name formals ic oc decls body kwd-alist) parsed)
       (pkg (current-package state))
       (wrld (w state))
       ;;some initialization
       ((mv start state) (acl2::read-run-time state))
       (kwd-alist (put-assoc :start-time start kwd-alist))
       ((er &) (assign defunc-failure-reason :none))
       (static-defunc-ev
        (defunc-events-with-staticp-flag
          name formals ic oc decls body kwd-alist wrld t d? pkg))
       (dynamic-defunc-ev
        (defunc-events-with-staticp-flag
          name formals ic oc decls body kwd-alist wrld nil d? pkg))
       (program-mode-defunc-ev
        (program-mode-defunc-events
         name formals ic oc decls body kwd-alist d? wrld pkg))
       (termination-strictp
        (and (get1 :termination-strictp kwd-alist)
             (not (get1 :program-mode-p kwd-alist))))
       ;;program-mode overrides termination-strictp
       (function-contract-strictp
        (get1 :function-contract-strictp kwd-alist))
       (make-undef (make-undefined-aux parsed wrld d? t pkg))
       (events-seen-t   (cons make-undef (events-seen-list parsed wrld t d? pkg)))
       (events-seen-nil (cons make-undef (events-seen-list parsed wrld nil d? pkg))))
    (value
     (cond
      ((and termination-strictp function-contract-strictp)
       `(:OR ,static-defunc-ev
             ,(make-show-failure-msg-ev start kwd-alist events-seen-t)))
      (termination-strictp
       `(:OR ,static-defunc-ev
             ,dynamic-defunc-ev
             ,(make-show-failure-msg-ev start kwd-alist events-seen-nil)))
      (t `(:OR ,static-defunc-ev
               ,dynamic-defunc-ev
               ,program-mode-defunc-ev
               ,(make-show-failure-msg-ev
                 start kwd-alist
                 (list (make-defun-no-guard-ev
                        name formals ic oc decls body kwd-alist wrld t d? pkg)))))))))

#|
(defmacro defunc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                       (and lst (cadr lst))))))
    `(encapsulate
      nil
      (make-event (make-undefined ',name ',args nil (current-package state) (w state)))
      (with-output
       ,@(and (not verbosep) '(:off :all))
       :gag-mode ,(not verbosep)
       :stack :push
       ;; Generate undef
       (make-event
        (er-progn
         ;; Test phase using trans-eval/make-event
         (test?-phase (parse-defunc ',name ',args (current-package state) (w state)) state)
         ;; Generate events
         (defunc-events (parse-defunc ',name ',args (current-package state) (w state)) nil state)))))))
|#

(defmacro defunc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                       (and lst (cadr lst))))))
    `(with-output
      ,@(and (not verbosep) '(:off :all))
      :gag-mode ,(not verbosep)
      :stack :push
      (encapsulate
       nil
       (with-output
      ,@(and (not verbosep) '(:off :all)) :on (error)
        (make-event
         (make-undefined ',name ',args nil (current-package state) (w state))))
       (make-event
        (er-progn
         ;; Test phase using trans-eval/make-event
         (test?-phase
          (parse-defunc ',name ',args (current-package state) (w state)) state)
         ;; Generate events
         (defunc-events
           (parse-defunc ',name ',args (current-package state) (w state)) nil state)))))))

(defmacro defundc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                       (and lst (cadr lst))))))
    `(with-output
      ,@(and (not verbosep) '(:off :all))
      :gag-mode ,(not verbosep)
      :stack :push
      (encapsulate
       nil
       (with-output
        ,@(and (not verbosep) '(:off :all)) :on (error)
        (make-event
         (make-undefined ',name ',args t (current-package state) (w state))))
       (make-event
        (er-progn
         ;; Test phase using trans-eval/make-event
         (test?-phase
          (parse-defunc ',name ',args (current-package state) (w state)) state)
         ;; Generate events
         (defunc-events
           (parse-defunc ',name ',args (current-package state) (w state)) t state)))))))

#|
(defmacro defundc (name &rest args)
  (b* ((verbosep (let ((lst (member :verbose args)))
                   (and lst (cadr lst))))
       (verbosep (or verbosep
                     (let ((lst (member :debug args)))
                       (and lst (cadr lst))))))
    `(encapsulate
      nil
      (make-event (make-undefined ',name ',args t (current-package state) (w state)))
      (with-output
       ,@(and (not verbosep) '(:off :all))
       :gag-mode ,(not verbosep)
       :stack :push
       ;; Generate undef
       (make-event
        (er-progn
         ;; Test phase using trans-eval/make-event
         (test?-phase
          (parse-defunc ',name ',args (current-package state) (w state)) state)
         ;; Generate events
         (defunc-events
           (parse-defunc ',name ',args (current-package state) (w state)) t state)))))))
|#

(include-book "xdoc/top" :dir :system)

(defxdoc defunc
  :parents (acl2::acl2-sedan acl2::macro-libraries)
  :short "Function definitions with contracts @(see acl2::defun)"
  :long
  "
<h3>Examples</h3>

@({

  (defunc len (a)
    :input-contract t
    :output-contract (natp (len a))
    (if (atom a)
        0
      (+ 1 (len (rest a)))))

  (defunc app (x y)
    :input-contract (and (true-listp x) (true-listp y))
    :output-contract (and (true-listp (app x y))
                          (equal (len (app x y)) (+ (len x) (len y))))
    (if (endp x)
        y
      (cons (car x) (app (cdr x) y))))

  (defunc add-digits (x)
    :input-contract (natp x)
    :output-contract (natp (add-digits x))
    :function-contract-hints ((\"Goal\" :do-not '(acl2::generalize)))
    (if (< x 10)
        x
      (let* ((rem (rem x 10))
             (y   (/ (- x rem) 10)))
        (+ rem (add-digits y)))))

  (defunc square-list (l)
    :input-contract (nat-listp l)
    :output-contract (nat-listp (square-list l))
    (if (endp l)
        nil
      (app (list (* (car l) (car l)))
           (square-list (cdr l))))
    :verbose t
    :skip-tests t)

})

<h3>Purpose</h3>
<p>
The macro @('defunc') is an extension of @('acl2::defun') with <b>contracts</b>.
</p>

<p> Using @('defunc') one can specify input and output
contracts (pre and post conditions) for a function. The following
actions are performed when @('defunc') is used in the default
way. If any of the actions fail, then an informative error
message is printed. If all actions succeed, then the function has
been successfully admitted to ACL2s.  </p>

<ol>

<li> Test the function contract, i.e., whether the output
contract holds under the assumption that the function terminates
and the input contract holds.</li>

<li> Test the body contracts, i.e., whether the contracts of the
functions appearing in the body of the @('defunc') are violated.
</li>

<li>Construct a definition in the core ACL2 logic that respects
the input contracts, and prove that this definition is
terminating.</li>

<li> Prove the function contract, i.e., that the input
contract implies the output contract.</li>

<li> Prove the body contracts, i.e., that for each occurrence of
a function call inside the body of the function being defined,
all of the arguments to the function call satisfy the input
contracts of the function. In ACL2 parlance, this is guard
verification.</li>

<li> Replace the function definition and induction scheme with a
definition rule and an induction scheme for the function that
restricts definition expansion and inductions to contexts where
the input contract is satisfied. If @('defunc') is used in a
disciplined way, then all contexts should satisfy this
restriction.  Use @(':pcb fun-name') to check the names of the
above events.  </li>
</ol>


<h3>Syntax</h3>
<p>
The general form of @('defunc') is:
</p>

@({
 (defunc name (x1 x2 ...)
   [doc-string declare-form*]
   [:input-contract ic]
   [:output-contract oc]
   [:function-contract-hints hints :rule-classes ...] ;function contract hints
   [:body-contracts-hints hints]                      ;body contracts hints
   [Other :key value ...]
   body)
})

<p>
The form of @('defunc') is just like @(see acl2::defun) except that is allows
extra keyword options.  Note that the keyword options can go anywhere
between the formals (parameters) and the end of @('defunc') macro.
The supported keyword options with the syntax restrictions and actions are noted
below.
</p>

<h4>Keyword Options</h4>

<dl>
<dt>@(':input-contract ic')</dt>
  <dd>Required; @('ic') is a <see topic='@(url acl2::term)'>term</see>.</dd>
<dt>@(':output-contract oc')</dt>
  <dd>Required; @('oc') is a <see topic='@(url acl2::term)'>term</see>.</dd>
<dt>@(':function-contract-hints hints')</dt>
  <dd>Passed as <tt>:<see topic='@(url acl2::hints)'>hints</see></tt> to the
      function contract @(see defthm).</dd>
<dt>@(':rule-classes rcs')<br/>
    @(':instructions is')<br/>
    @(':otf-flg flg')</dt>
  <dd>These three keyword arguments are passed directly to the function
      contract @(see defthm).</dd>
<dt>@(':body-contracts-hints hints')</dt>
  <dd>Passed as <tt>:<see topic='@(url acl2::hints)'>hints</see></tt> to the
      body contracts @(see defthm).</dd>
</dl>

<p>The following keyword options are usually set at the
session-wide-level (see the <tt>set-defunc-*</tt> macros documented
below); when given as keyword arguments to @('defunc') they override
the session defaults.</p>

<dl>
<dt>@(':termination-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if termination failed.</dd>
  <dd>When @('x') is @('nil'), then if termination fails, admit the function in
      :program mode.</dd>
<dt>@(':function-contract-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if the contract proof failed.</dd>
  <dd>When @('x') is @('nil'), then if the proof fails, add a dynamic contract
      check.</dd>
<dt>@(':body-contracts-strictp x')</dt>
  <dd>When @('x') is @('t') (default), abort if the body contracts proof
      failed.</dd>
  <dd>When @('x') is @('nil'), body contracts are checked dynamically.</dd>
<dt>@(':timeout n')</dt>
  <dd>Limit the time spent in defunc events to @('n') seconds.</dd>
<dt>@(':skip-tests t')</dt>
  <dd>Skip the testing actions.</dd>
</dl>


<h3>Debugging</h3>
<p>
To debug a failed defunc form, you can proceed in multiple ways:
<ul>
<li> Submit the events shown above the failure message to replicate the error.</li>
<li> At the session editor (or emacs prompt), submit/evaluate
     @(':trans1 (defunc ...)')
     And from the output, evaluate the form that says <tt>(defunc-events ...)</tt>.</li>
<li>Use keyword options <tt>:verbose t</tt> (or <tt>:debug t</tt>) and examine the ACL2 output.</li>
</ul>
</p>
"
  )

(defmacro set-defunc-termination-strictp (b)
  (tbl-set-fn 'defunc-defaults-table :termination-strictp b))
(defmacro set-defunc-function-contract-strictp (b)
  (tbl-set-fn 'defunc-defaults-table :function-contract-strictp b))
(defmacro set-defunc-force-ic-hyps-in-definitionp (b)
  (tbl-set-fn 'defunc-defaults-table :force-ic-hyps-in-definitionp b))
(defmacro set-defunc-force-ic-hyps-in-contract-thmp (b)
  (tbl-set-fn 'defunc-defaults-table :force-ic-hyps-in-contract-thmp b))
(defmacro set-defunc-body-contracts-strictp (b)
  (tbl-set-fn 'defunc-defaults-table :body-contracts-strictp b))
(defmacro set-defunc-timeout (r)
  (tbl-set-fn 'defunc-defaults-table :timeout r))


(defmacro set-defunc-skip-admissibilityp (b)
  (tbl-set-fn 'defunc-defaults-table :skip-admissibilityp b))
(defmacro set-defunc-skip-function-contractp (b)
  (tbl-set-fn 'defunc-defaults-table :skip-function-contractp b))
(defmacro set-defunc-skip-body-contractsp (b)
  (tbl-set-fn 'defunc-defaults-table :skip-body-contractsp b))

(defmacro get-defunc-termination-strictp ()
  (tbl-get-fn 'defunc-defaults-table :termination-strictp))
(defmacro get-defunc-function-contract-strictp ()
  (tbl-get-fn 'defunc-defaults-table :function-contract-strictp))
(defmacro get-defunc-force-ic-hyps-in-definitionp ()
  (tbl-get-fn 'defunc-defaults-table :force-ic-hyps-in-definitionp))
(defmacro get-defunc-force-ic-hyps-in-contract-thmp ()
  (tbl-get-fn 'defunc-defaults-table :force-ic-hyps-in-contract-thmp))
(defmacro get-defunc-body-contracts-strictp ()
  (tbl-get-fn 'defunc-defaults-table :body-contracts-strictp))
(defmacro get-defunc-timeout ()
  (tbl-get-fn 'defunc-defaults-table :timeout))

(defmacro get-defunc-skip-admissibilityp ()
  (tbl-get-fn 'defunc-defaults-table :skip-admissibilityp))
(defmacro get-defunc-skip-function-contractp ()
  (tbl-get-fn 'defunc-defaults-table :skip-function-contractp))
(defmacro get-defunc-skip-body-contractsp ()
  (tbl-get-fn 'defunc-defaults-table :skip-body-contractsp))

(defxdoc set-defunc-timeout
  :parents (defunc)
  :short "Set timeout (in seconds) for defunc"
  :long
  "<p>Set timeout for the events generated by @('defunc').
  The default timeout limit is set to 50 seconds.</p>

  <p>Guard : Timeout value should be a rational.</p>
   ")

(defxdoc get-defunc-timeout
  :parents (defunc)
  :short "Get timeout default for defunc")

(defxdoc get-defunc-termination-strictp
  :parents (defunc)
  :short "Get termination-strictp default for defunc")

(defxdoc get-defunc-function-contract-strictp
  :parents (defunc)
  :short "Get function-contract-strictp default for defunc")

(defxdoc get-defunc-force-ic-hyps-in-definitionp
  :parents (defunc)
  :short "Get force-ic-hyps-in-definitionp default for defunc")

(defxdoc get-defunc-force-ic-hyps-in-contract-thmp
  :parents (defunc)
  :short "Get force-ic-hyps-in-contract-thmp default for defunc")

(defxdoc get-defunc-body-contracts-strictp
  :parents (defunc)
  :short "Get body-contracts-strictp default for defunc")


(defxdoc set-defunc-termination-strictp
  :parents (defunc)
  :short "Set termination-strictp for defunc"
  :long
  "<p>Set whether termination is strict for @('defunc'), i.e. whether
   @('defunc') should abort or continue on failure to prove termination.</p>
   <p>The default is set to @('t').</p>
   ")

(defxdoc set-defunc-function-contract-strictp
  :parents (defunc)
  :short "Set function-contract-strictp for defunc"
  :long
  "<p>Set whether @('defunc') should abort or continue on failure to prove function contract.</p>
   <p>The default is set to @('t').</p>
   ")

(defxdoc set-defunc-force-ic-hyps-in-definitionp
  :parents (defunc)
  :short "Set force-ic-hyps-in-definitionp for defunc"
  :long
  "<p>Set whether @('defunc') should force the hypotheses (input contract) in the definition rules it generates.</p>
   <p>The default is set to @('nil').</p>
   ")

(defxdoc set-defunc-force-ic-hyps-in-contract-thmp
  :parents (defunc)
  :short "Set force-ic-hyps-in-contract-thmp for defunc"
  :long
  "<p>Set whether @('defunc') should force the hypotheses in the contract theorems it generates.</p>
   <p>The default is set to @('t').</p>
   ")

(defxdoc set-defunc-body-contracts-strictp
  :parents (defunc)
  :short "Set body-contracts-strictp for defunc"
  :long
  "<p>Set whether @('defunc') should abort or continue on failure to verify body contracts.</p>
   <p>The default is set to @('t').</p>
   ")

(defmacro defuncd (name &rest args)
  `(encapsulate
    nil
    (defunc ,name ,@args)
    (make-event 
     `(in-theory
       (disable
        ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))

(defmacro set-defunc-skip-tests (r)
  (tbl-set-fn 'defunc-defaults-table :skip-tests r))

(defmacro defunc-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defunc ,name ,@args)))

(defmacro defuncd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defuncd ,name ,@args)))

(defmacro defundcd (name &rest args)
  `(encapsulate
    nil
    (defundc ,name ,@args)
    (make-event 
     `(in-theory
       (disable
        ,(make-symbl `(,',name -DEFINITION-RULE) (current-package state)))))))

(defmacro defundc-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defundc ,name ,@args)))

(defmacro defundcd-no-test (name &rest args)
  `(acl2::with-outer-locals
    (local (acl2s-defaults :set testing-enabled nil))
    (defundcd ,name ,@args)))
