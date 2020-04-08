#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
builtin combinators (oneof, member, range) in core defdata language
author: harshrc
file name: builtin-combinators.lisp
date created: [2014-08-06 Sun]
data last modified: [2017-06-22 Thu]
|#

(in-package "DEFDATA")

(include-book "std/util/bstar" :dir :system)

(table defdata-defaults-table nil
       '((:debug       .  nil)
         (:print-commentary . t)
         (:print-summary  . nil)
         (:time-track     . t)
         (:testing-enabled . :naive)
         (:disable-non-recursive-p . nil)

; The following are quite stable and there is no reason for these to be overridden
         (:pred-suffix . "p") ;unused
         ;; (:pred-prefix . "")
         ;; (:enum-prefix . "nth-")
         ;; (:enum-suffix . "")
         ;; (:enum/acc-prefix . "nth-")
         ;; (:enum/acc-suffix . "/acc")
         (:pred-guard  .  (lambda (x) t))
         (:enum-guard  .  (lambda (x) (natp x)))
         (:enum/acc-guard . (lambda (m seed) (and (natp m) (unsigned-byte-p 31 seed))))


; The following 4 defaults shouldnt be overridden by user (of defdata
; macro) but only by implementors and extenders of defdata framework.
         (:pre-pred-hook-fns . nil)
         (:post-pred-hook-fns . nil)
         (:pre-hook-fns . nil)
         (:post-hook-fns . nil)
         )
       :clear)


; BUILTIN COMBINATOR TABLE

(defun member-pred-I (x s) `(and (member-equal ,x ,(cadr s)) t))
(defun member-enum-I (i s) `(nth (mod ,i (len ,(cadr s))) ,(cadr s)))
(defun member-enum/acc-I (i s)
  (declare (ignorable i))
  `(mv-let (idx _SEED)
           (random-index-seed (len ,(cadr s)) _SEED)
           (mv (nth idx ,(cadr s)) (the (unsigned-byte 31) _SEED))))



(defun get-tau-int (domain rexp)
  (declare (xargs :verify-guards t))
  (let ((dom (if (eq domain 'acl2s::integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi)
     (b* ((lo-rel (eq lo-rel-sym '<))
          (hi-rel (eq hi-rel-sym '<))
          (lo (and (rationalp lo) lo))
          (hi (and (rationalp hi) hi)))
       (acl2::make-tau-interval dom lo-rel lo hi-rel hi))))))

(defun make-acl2-range-constraints (x domain rexp)
  (let ((dom (if (eq domain 'acl2s::integer)
                 'acl2::integerp
               'acl2::rationalp)))
  (case-match rexp
    ((lo lo-rel-sym '_ hi-rel-sym hi)
     `((,dom ,x)
       ,@(and (rationalp lo) `((,lo-rel-sym ,lo ,x)))
       ,@(and (rationalp hi) `((,hi-rel-sym ,x  ,hi))))))))


;(defun range-pred-I (x s) `(acl2::in-tau-intervalp ,x ',(get-tau-int (cadr s) (third s))))
(defun range-pred-I (x s) `(AND . ,(make-acl2-range-constraints x (cadr s) (third s))))


(defun make-enum-body-for-range (r domain lo hi lo-rel hi-rel)
    (case domain
      (acl2s::integer (let ((lo (and lo (if lo-rel (1+ lo) lo))) ;make both inclusive bounds
                           (hi (and hi (if hi-rel (1- hi) hi))))
                        (cond ((and lo hi)
                               `(acl2s::nth-integer-between ,r ,lo ,hi))

                             (lo ;hi is positive infinity
                              `(+ ,lo (acl2s::nth-nat-testing ,r)))

                             ((posp hi) ;lo is neg infinity and hi is >=1
                              `(let ((i-ans (acl2s::nth-integer ,r)))
                                 (if (> i-ans ,hi)
                                     (mod i-ans (1+ ,hi))
                                   i-ans))) ;ans shud be less than or equal to hi
                             
                             
                             (t ;lo is neg inf, and hi is <= 0
                              `(- ,hi (acl2s::nth-nat-testing ,r)))))) ;ans shud be less than or equal to hi
      
      (otherwise  (let* ((gap (/ (- (rfix hi) (rfix lo)) 1000))
                        (lo (and lo (if lo-rel (+ gap lo) lo))) ;make both inclusive bounds
                        (hi (and hi (if hi-rel (- hi gap) hi))))
                    (cond ((and lo hi)
                         `(acl2s::nth-rational-between ,r ,lo ,hi))

                        (lo ;hi is positive infinity
                         `(+ ,lo (acl2s::nth-pos-rational-testing ,r)))
                        
                        ((> hi 0) ;lo is neg infinity and hi is is >= 1
                         `(let ((rat-ans (acl2s::nth-rational ,r)))
                            (if (> rat-ans ,hi)
                                (mod rat-ans (1+ ,hi))
                              rat-ans))) ;ans shud be less than or equal to hi
                        
                        (t ;lo is neg infinity and hi is is <= 0
                         `(- ,hi (acl2s::nth-pos-rational-testing ,r))))))))

(defun range-enum-I (i s)
  (b* ((tau-interval (get-tau-int (cadr s) (third s)))
       (lo (tau-interval-lo tau-interval))
       (hi (tau-interval-hi tau-interval))
       (lo-rel (tau-interval-lo-rel tau-interval))
       (hi-rel (tau-interval-hi-rel tau-interval)))
    (make-enum-body-for-range i (cadr s) lo hi lo-rel hi-rel)))


(defun minimum-range-lo-builtin ()
  (declare (xargs :guard t))
  -1000); (- 0 (expt 2 32)))
(defun maximum-range-hi-builtin ()
  (declare (xargs :guard t))
  1000); (+ 0 (expt 2 32)))
(defstub minimum-range-lo () => *)
(defstub maximum-range-hi () => *)
(defattach minimum-range-lo minimum-range-lo-builtin)
(defattach maximum-range-hi maximum-range-hi-builtin)
#| Sampling distribution for Bounded Ranges [2017-06-21 Wed]
.01 min, .01 max, .01 mid1, .01 mid2
    (or .02 if one mid, eg 1-4 has 2 mids: 2,3, but 1-5 has one: 3)
.10 uniform between -100 and 100 (added by harshrc)
.19 geometric around mid
.45 uniform between min-max
.1 geometric around min (ie, [min---])
.1 geometric around max (ie, [max--])
.01 geometric [max+1 ...])
.01 geometric [min-1 ...])
|#

;; The keys should add up to 100
(defun sampling-dist-default (min max mid1 mid2)
  (b* ((small-low (if (< min -100) -100 min))
       (small-hi (if (> max 100) 100 max)))
    `((1 :eq ,min)
      (1 :eq ,max)
      (1 :eq ,mid1)
      (1 :eq ,mid2)
      (10 :uniform ,small-low ,small-hi)
      (19 :geometric :around ,mid1)
      (47 :uniform ,min ,max)
      (10 :geometric :leq ,max)
      (10 :geometric :geq ,min)
;     (1 :geometric :geq ,(1+ max))
;     (1 :geometric :leq ,(1- min))
      )))

#|

(defun test-weighted-switch-nat (wts n seed. acc)
  (if (zp n)
      (mv acc seed.)
    (b* (((mv idx (the (unsigned-byte 31) seed.))
          (defdata::random-index-seed 100 seed.))
         ((mv x &) (defdata::weighted-switch-nat wts idx))
         ((mv acc seed.) (test-weighted-switch-nat wts (1- n) seed. (update-nth x (1+ (nth x acc)) acc))))
      (mv acc seed.))))

(u::defloop list-div-mult-by (xs div mult)
            (for ((x in xs)) (collect (* (/ x div) mult))))

(defun test-weighted-switch-nat-top (wts n state)
  (declare (xargs :stobjs (state) :verify-guards nil))
  (b* ((acc (make-list (len wts) :initial-element 0))
       ((mv acc seed.) (test-weighted-switch-nat wts n (defdata::getseed state) acc))
       (state (defdata::putseed seed. state)))
    (value (list-div-mult-by acc n 100))))

(test-weighted-switch-nat-top '(1 1 1 1 29 45 10 10 1 1) 10000 state)

(defun test-enum-dist (n state)
  (declare (xargs :stobjs (state) :verify-guards nil))
  (if (zp n)
      (cw "~%")
  (b* (((mv x seed.) (NTH-SRL-INT/ACC 0 (defdata::getseed state) acc))
       (state (defdata::putseed seed. state)))
    (prog2$ (cw "~x0  " x)
            (test-enum-dist (1- n) state)))))




|#
(defun sampling-dist-lo (min max mid1 mid2)
  (b* ((small-low (if (< min -100) -100 min))
       (small-hi (if (> max 100) 100 max)))
    `((1 :eq ,min)
      (1 :eq ,max)
      (1 :eq ,mid1)
      (1 :eq ,mid2)
      (1 :geometric :around ,mid1)
      (22 :uniform ,min ,max)
      (1 :geometric :leq ,max)
      (32 :uniform ,small-low ,small-hi)
      (40 :geometric :geq ,min)
;      (1 :geometric :geq ,(1+ max))
;      (1 :geometric :leq ,(1- min))
      )))

(defun sampling-dist-hi (min max mid1 mid2)
  (b* ((small-low (if (< min -100) -100 min))
       (small-hi (if (> max 100) 100 max)))
    `((1 :eq ,min)
      (1 :eq ,max)
      (1 :eq ,mid1)
      (1 :eq ,mid2)
      (1 :geometric :around ,mid1)
      (22 :uniform ,min ,max)
      (32 :uniform ,small-low ,small-hi)
      (40 :geometric :leq ,max)
      (1 :geometric :geq ,min)
;      (1 :geometric :geq ,(1+ max))
;      (1 :geometric :leq ,(1- min))
      )))

(defun midpoints (lo hi)
  (if (and (integerp lo) (integerp hi)
           (oddp (- hi lo)))
      (let ((half2 (/ (1+ (- hi lo)) 2)))
        (mv (1- (+ lo half2)) (+ lo half2)))
    (let ((half1 (/ (- hi lo) 2)))
      (mv (+ lo half1) (+ lo half1)))))

(defun make-enum-exp-for-bounded-range (ivar seedvar dom sampling-dist)
  (b* ((weights (strip-cars sampling-dist))
       (ctx 'make-enum-exp-for-bounded-range)
       (nth-fn (if (eq dom 'acl2s::integer)
                   'acl2s::nth-integer
                 'acl2s::nth-rational))
       (nth-pos-fn (if (eq dom 'acl2s::integer)
                       'acl2s::nth-nat
                     'acl2s::nth-pos-rational))
       (between-fn (if (eq dom 'acl2s::integer)
                       'defdata::random-integer-between-seed
                     'defdata::random-rational-between-seed)))


    `(b* (((mv idx (the (unsigned-byte 31) ,seedvar))
           (defdata::random-index-seed 100 ,seedvar))
          ((mv choice &) (defdata::weighted-switch-nat ',weights idx))
          (chosen (nth choice ',sampling-dist))
          (sp (cdr chosen)))
       (case-match sp ;sampling type dispatch
         ((':eq x) (mv x ,seedvar))
         ((':geometric ':around x)  (mv (+ x (,nth-fn ,ivar)) ,seedvar))
         ((':geometric ':leq x)     (mv (- x (,nth-pos-fn ,ivar)) ,seedvar))
         ((':geometric ':geq x)     (mv (+ x (,nth-pos-fn ,ivar)) ,seedvar))
         ((':uniform x1 x2)         (,between-fn x1 x2 ,seedvar))
         (& (mv (er hard ',ctx "~| Impossible case ~x0.~%" sp) ,seedvar))))))


(defun make-enum/acc-body-for-range (ivar seedvar domain lo hi lo-rel hi-rel)
  (b* ((gap (if (eq domain 'acl2s::integer)
                1
              (/ (- (rfix hi) (rfix lo)) 1000)))
       (lo (and lo (if lo-rel (+ gap lo) lo))) ;make both inclusive bounds
       (hi (and hi (if hi-rel (- hi gap) hi)))
       (lo1 (or lo (minimum-range-lo)))
       (hi1 (or hi (maximum-range-hi)))
       ((mv mid1 mid2) (midpoints lo1 hi1))
       (exp (cond ((and lo hi)
                   (make-enum-exp-for-bounded-range
                    ivar seedvar domain (sampling-dist-default lo hi mid1 mid2)))
                  (lo (make-enum-exp-for-bounded-range
                       ivar seedvar domain (sampling-dist-lo lo hi1 mid1 mid2)))
                  (t (make-enum-exp-for-bounded-range
                       ivar seedvar domain (sampling-dist-hi lo1 hi1 mid1 mid2))))))

    `(mv-let (,ivar ,seedvar)
             (random-natural-seed ,seedvar) ;;overwrite original value of ivar
             (declare (ignorable ,ivar))
             ,exp)))

(defun range-enum/acc-I (ivar s)
  (declare (ignorable ivar))
  (b* ((tau-interval (get-tau-int (cadr s) (third s)))
       (lo (tau-interval-lo tau-interval))
       (hi (tau-interval-hi tau-interval))
       (lo-rel (tau-interval-lo-rel tau-interval))
       (hi-rel (tau-interval-hi-rel tau-interval)))
    (make-enum/acc-body-for-range ivar '_SEED (cadr s) lo hi lo-rel hi-rel)))





(include-book "defdata-util")
(defun make-defconst-event1 (p top-kwd-alist wrld)
  (declare (ignorable top-kwd-alist wrld))
  (b* (((cons tname A) p)
       ((acl2::assocs ndef) A)
       (nbody ndef)
       (curr-pkg (get1 :current-package top-kwd-alist))
       (name (s+ "*" tname "-VALUES*" :pkg curr-pkg)))
    (if (and (consp nbody) (eq 'acl2s::member (car nbody)))
        `((acl2::defconst-fast ,name ,(cadr nbody)))
      '())))


(defloop member-defconst-event (ps kwd-alist wrld)
  (for ((p in ps)) (append (make-defconst-event1  p kwd-alist wrld))))

(add-pre-post-hook defdata-defaults-table :pre-pred-hook-fns '(member-defconst-event))

#!ACL2S
(table defdata::builtin-combinator-table nil
       '((or . ((:aliases . (oneof or anyof acl2::or acl2::oneof acl2::anyof))
                (:arity . t)
                (:pred-I . nil) ; no special handling.
                (:pred-inverse-I . nil)
                (:enum-I . nil)
                (:enum/acc-I . nil)))

         (member . ((:aliases . (enum member member-eq member-equal in acl2::enum acl2::in))
                    (:arity . 1)
                    (:pred-I . defdata::member-pred-I)
                    (:pred-inverse-I . nil)
                    (:enum-I . defdata::member-enum-I)
                    (:enum/acc-I . defdata::member-enum/acc-I)
                    ))

         (range . ((:aliases . (range between acl2::range acl2::between))
                   (:arity . 2)
                   (:pred-I . defdata::range-pred-I)
                   (:pred-inverse-I . nil)
                   (:enum-I . defdata::range-enum-I)
                   (:enum/acc-I . defdata::range-enum/acc-I))))

       :clear)




;copied from cgen./utilities


; Matt K. mod, 10/2017: Since ev-fncall-w is called in my-ev-w but is now
; untouchable, a change is necessary.  Fortunately, cert.acl2 specifies :ttags
; :all, so we can introduce a trust tag to remove ev-fncall-w as an
; untouchable.  An alternate solution, not yet tried (at least by me), is to
; use ev-fncall-w! instead; but that might slow things down a lot because of
; the extra checking done.  Note that magic-ev-fncall isn't an option, because
; state isn't available in my-ev-w.

(defttag :ev-fncall-w-ok)
(remove-untouchable acl2::ev-fncall-w t)
(defttag nil)

(mutual-recursion
;(ev-fncall-w FN ARGS W SAFE-MODE GC-OFF HARD-ERROR-RETURNS-NILP AOK)
;I use sumners default values for
;               nil    ; safe-mode
;               t      ; gc-off
;               nil    ; hard-error-returns-nilp
;               nil    ; aok


(defun my-ev-w (term alist ctx w hard-error-returns-nilp)
"special eval function that does not need state and
cannot handle if, return-last,mv-list, stobjs, wormhole etc
very restrictive
Mainly to be used for evaluating enum lists "
;Close to ev-rec in translate.lisp
(declare (xargs :mode :program
                :guard (and (acl2::termp term w)
                            (plist-worldp w)
                            (symbol-alistp alist)
                            (booleanp hard-error-returns-nilp))))

(b* (((when (acl2::variablep term))
;variable expression
      (let ((v (assoc-eq term alist))) ;bugfix (removed cdr).
;(earlier, if term had a value NIL, we were errorneusly
;crashing!!!
        (if v ;not null
          (mv nil (cdr v))
          (prog2$
           (er hard ctx "Unbound variable ~x0.~%" term)
           (mv t term)))))
;quoted expression
     ((when (acl2::fquotep term))
      (mv nil (cadr term)))
;if expression
     ((when (eq (car term) 'if))
      (prog2$
       (er hard ctx "IF expressions not supported at the moment.~%")
       (mv t term)))
;function expression
     ((mv args-er args)
      (my-ev-w-lst (cdr term) alist ctx
                   w hard-error-returns-nilp))
     ((when args-er)
      (prog2$
       (er hard ctx "Eval args failed~%")
       (mv t term)))
     ((when (acl2::flambda-applicationp term))
      (my-ev-w (acl2::lambda-body (car term))
               (acl2::pairlis$ (acl2::lambda-formals (car term)) args)
               ctx w hard-error-returns-nilp)))
    (acl2::ev-fncall-w (car term) args w
                       nil nil t hard-error-returns-nilp nil)))

(defun my-ev-w-lst (term-lst alist
                             ctx w hard-error-returns-nilp)
"special eval function that does not need state and
cannot handle return-last,mv-list, stobjs, wormhole etc
very restrictive
Mainly to be used for evaluating enum lists "
;Close to ev-rec-lst in translate.lisp
(declare (xargs :mode :program
                :guard (and (acl2::term-listp term-lst w)
                            (plist-worldp w)
                            (symbol-alistp alist)
                            (booleanp hard-error-returns-nilp))))
(if (endp term-lst)
    (mv nil nil)
  (b* (((mv erp1 car-ans)
        (my-ev-w (car term-lst) alist
                 ctx w hard-error-returns-nilp))
       ((when erp1)
        (prog2$
         (er hard ctx "eval ~x0 failed~%" (car term-lst))
         (mv t term-lst)))
       ((mv erp2 cdr-ans)
        (my-ev-w-lst (cdr term-lst) alist
                     ctx w hard-error-returns-nilp))
       ((when erp2)
        (prog2$
         (er hard ctx "eval failed~%")
         (mv t term-lst))))
    (mv nil (cons car-ans cdr-ans)))))
)

(push-untouchable acl2::ev-fncall-w t) ; see Matt K. comment above

(defun trans-my-ev-w (form ctx w hard-error-returns-nilp)
  (declare (xargs :mode :program
                  :guard (and (plist-worldp w)
                              (booleanp hard-error-returns-nilp))))

  (mv-let
   (erp term x)
   (acl2::translate11 form nil nil nil nil nil nil
                      ctx w (acl2::default-state-vars nil))
   (declare (ignore x))
   (if erp
       (if hard-error-returns-nilp
           (mv erp form)
         (prog2$
          (er hard ctx "~x0 could not be translated.~%" form)
          (mv erp form)))
     (my-ev-w term nil ctx w hard-error-returns-nilp))))


(defun bad-range-syntax (rexp)
  (er hard? 'parse-range-exp
"~| Range exp ~x0 is not of the following form: ~
     ~| (lo < _ < hi) or (lo < _ < hi)  where ~
     ~| <= can be used as the comparison relation and one of the comparisons can be dropped i.e ~
     ~| (lo <= _), (_ <= hi) etc.~%" rexp))


(set-ignore-ok t)
;TODO BAD idea to rely on symbols for < and <= (ACL2S B::< is different from <
;here -- this caused a bug)
;; (defun preprocess-range-exp (rexp)
;;   (case-match rexp
;;     ((lo '< '_ '< hi) rexp)
;;     ((lo '< '_ '<= hi) rexp)
;;     ((lo '<= '_ '< hi) rexp)
;;     ((lo '<= '_ '<= hi) rexp)

;;     ((lo '< '_) `(,lo < _ < nil))
;;     (('_ '< hi) `(nil < _ < ,hi))


;;     ((lo '<= '_) `(,lo <= _ < nil))
;;     (('_ '<= hi) `(nil < _ <= ,hi))
;;     (& rexp)))

(defun pp-rel (rel-sym)
  (if (equal (symbol-name rel-sym) "<")
      '<
    '<=))

(defun pp-range-exp (rexp)
  "preprocess range expression"
  (case-match rexp
    ((lo lo-rel '_ hi-rel hi) (list lo (pp-rel lo-rel) '_ (pp-rel hi-rel) hi))
    ((lo lo-rel '_)           (list lo (pp-rel lo-rel) '_ '< nil))
    (('_ hi-rel hi)           (list nil '< '_ (pp-rel hi-rel) hi))

    (& (bad-range-syntax rexp))))

(set-ignore-ok nil)

(defun parse-range-exp (rexp1 domain ctx wrld)
  (declare (xargs :mode :program))
  (let ((rexp (pp-range-exp rexp1)))
  (case-match rexp
    ((lo-sym lo-rel-sym '_ hi-rel-sym hi-sym)
     (b* ((lo-rel (not (eq lo-rel-sym '<=)))
          (hi-rel (not (eq hi-rel-sym '<=)))
          ((mv erp hi)
           (trans-my-ev-w hi-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" hi-sym))
          ((mv erp lo)
           (trans-my-ev-w lo-sym ctx wrld nil))
          ((when erp)
           (er hard ctx "Evaluating rational expression ~x0 failed!~%" lo-sym))
          ((unless (and (or (null lo) (if (eq domain 'acl2s::integer) (integerp lo) (rationalp lo)))
                        (or (null hi) (if (eq domain 'acl2s::integer) (integerp hi) (rationalp hi)))
                        (not (and (null lo) (null hi)))))
           (er hard ctx "~| lo and hi in range expressions should evaluate to rationals, but instead got lo = ~x0 and hi = ~x1~%" lo hi))

          ((mv lo lo-rel) (if (eq domain 'acl2s::integer)
                              (if (and lo lo-rel)
                                  (mv (+ lo 1) nil)
                                (mv lo nil))
                            (mv lo lo-rel)))
          ((mv hi hi-rel) (if (eq domain 'acl2s::integer)
                              (if (and hi hi-rel)
                                  (mv (- hi 1) nil)
                                (mv hi nil))
                            (mv hi hi-rel)))

          ((when (and lo hi (eq domain 'acl2s::integer) (> lo hi)))
           (er hard ctx "~| lo <= hi should hold. But it does not: lo = ~x0 and hi = ~x1" lo hi))

          ((when (and lo hi (not lo-rel) (not hi-rel) (= lo hi))) lo)

          ((when (and lo hi (or lo-rel hi-rel) (>= lo hi)))
           (er hard ctx "~| lo < hi should hold. But it does not: lo = ~x0 and hi = ~x1" lo hi))

          (lo-rel-sym (if lo-rel '< '<=))
          (hi-rel-sym (if hi-rel '< '<=)))

       (list 'acl2s::range domain (list lo lo-rel-sym '_ hi-rel-sym hi))))
    (& (bad-range-syntax rexp1)))))

#|
(defun parse-enum-exp (eexp ctx w)
  (declare (xargs :mode :program))
  (b* (((when (proper-symbolp eexp)) eexp) ;name TODO.Bug -- But what if its not a name! We should catch this error...
       ((mv erp list-val) (trans-my-ev-w eexp ctx w nil))
       ((when erp)
        (er hard ctx "Evaluating list expression ~x0 failed!~%" eexp))
       ((unless (and (true-listp list-val) (consp list-val)))
        (er hard ctx "Enum argument ~x0 expected to be a non-empty list expression.~%" eexp)))
    (list 'acl2s::member (kwote list-val))))
|#

;; This removes duplicate elements and uses 'or, which works better
;; with tau because we can exactly characterize the type.
(defun parse-enum-exp (eexp ctx w)
  (declare (xargs :mode :program))
  (b* (((when (proper-symbolp eexp)) eexp) ;name TODO.Bug -- But what if its not a name! We should catch this error...
       ((mv erp list-val) (trans-my-ev-w eexp ctx w nil))
       ((when erp)
        (er hard ctx "Evaluating list expression ~x0 failed!~%" eexp))
       ((unless (and (true-listp list-val) (consp list-val)))
        (er hard ctx "Enum argument ~x0 expected to be a non-empty list expression.~%" eexp))
       (list-val (remove-duplicates list-val)))
    (if (consp (cdr list-val))
        (cons 'or (kwote-lst list-val))
      (kwote (car list-val)))))
