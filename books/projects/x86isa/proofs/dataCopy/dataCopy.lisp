;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-memory-utils" :dir :proof-utils :ttags :all)
(include-book "centaur/bitops/ihs-extensions" :dir :system)

(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

;; [Shilpi]: Move these events to the main books.

(defthmd rb-rb-subset
  ;; This theorem can be generalized so that the conclusion mentions addr1,
  ;; where addr1 <= addr.  Also, this is an expensive rule. Keep it disabled
  ;; generally.
  (implies (and (equal (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86))
                       bytes)
                (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (posp i)
                (< j i))
           (equal (mv-nth 1 (rb (create-canonical-address-list j addr) r-w-x x86))
                  (take j bytes)))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p) ()))))

(defthm take-and-rb
  (implies (and (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (< k i))
           (equal (take k (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86)))
                  (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p rb) ((:meta acl2::mv-nth-cons-meta))))))

(defthmd create-canonical-address-list-split
  (implies (and (canonical-address-p addr)
                (canonical-address-p (+ k addr))
                (natp j)
                (natp k))
           (equal (create-canonical-address-list (+ k j) addr)
                  (append (create-canonical-address-list k addr)
                          (create-canonical-address-list j (+ k addr)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p)
                                   ()))))
(defthm rb-rb-split-reads
  (implies (and (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (natp j)
                (natp k))
           (equal (mv-nth 1 (rb (create-canonical-address-list (+ k j) addr) r-w-x x86))
                  (append (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))
                          (mv-nth 1 (rb (create-canonical-address-list j (+ k addr)) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p)
                                   ((:meta acl2::mv-nth-cons-meta))))))

(defthm rb-returns-true-listp
  (implies (x86p x86)
           (true-listp (mv-nth 1 (rb addresses r-w-x x86))))
  :rule-classes (:rewrite :type-prescription))

(defthm create-canonical-address-list-of-0
  (equal (create-canonical-address-list 0 addr) nil))

(defthm zf-spec-thm
  (implies (not (equal x 0))
           (equal (zf-spec x) 0))
  :hints (("Goal" :in-theory (e/d* (zf-spec) ()))))

(defthm canonical-address-p-to-integerp-thm
  (implies (canonical-address-p x)
           (integerp x))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p) ())))
  :rule-classes :forward-chaining)

;; ======================================================================

;; Some GL Theorems:

(encapsulate
 ()
 (local (include-book "centaur/gl/gl" :dir :system))

 (def-gl-export loop-clk-measure-helper
   :hyp (and (signed-byte-p 64 m)
             (<= 4 m))
   :concl (< (loghead 64 (+ #xfffffffffffffffc m)) m)
   :g-bindings (gl::auto-bindings (:int m 64))
   :rule-classes :linear)

 (def-gl-export simplify-rax-expression
   :hyp (unsigned-byte-p 31 n)
   :concl (equal (logext 64 (ash (loghead 64 (logext 32 n)) 2))
                 (ash n 2))
   :g-bindings (gl::auto-bindings (:nat n 31)))


 (def-gl-export effects-copyData-loop-helper-1
   :hyp (and (<= 4 m)
             (unsigned-byte-p 33 m))
   :concl (equal (logext 64 (+ #xfffffffffffffffc m))
                 (loghead 64 (+ #xfffffffffffffffc m)))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-2
   :hyp (and (<= 4 m)
             (unsigned-byte-p 33 m))
   :concl (and (unsigned-byte-p 33 (loghead 64 (+ #xfffffffffffffffc m)))
               (signed-byte-p   64 (loghead 64 (+ #xfffffffffffffffc m))))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-3
   :hyp (and (<= 4 m)
             (unsigned-byte-p 33 m))
   :concl (< (loghead 64 (+ #xfffffffffffffffc m))
             *2^63*)
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes :linear)

 (def-gl-export effects-copyData-loop-helper-4
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (not (< (loghead 64 (+ #xfffffffffffffffc m))
                  4))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-5
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (mod (loghead 64 (+ #xfffffffffffffffc m)) 4) 0)
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-6
   :hyp (canonical-address-p src/dst)
   :concl (equal (logext 64 (+ 4 (loghead 64 src/dst)))
                 (+ 4 src/dst))
   :g-bindings (gl::auto-bindings (:int src/dst 64)))

 (def-gl-export effects-copyData-loop-helper-7
   :hyp (and (canonical-address-p src/dst)
             (canonical-address-p (+ m src/dst))
             (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (canonical-address-p (+ 4 src/dst (loghead 64 (+ #xfffffffffffffffc m))))
   :g-bindings (gl::auto-bindings (:mix (:int m 64)
                                        (:int src/dst 64))))

 (def-gl-export effects-copyData-loop-helper-8
   :hyp (and (canonical-address-p src/dst)
             (canonical-address-p (+ m src/dst))
             (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (canonical-address-p (+ (loghead 64 (+ #xfffffffffffffffc m))
                                  ;; (logext 64 (+ 4 (loghead 64 src/dst)))
                                  (+ 4 src/dst)
                                  ))
   :g-bindings (gl::auto-bindings (:mix (:int m 64)
                                        (:int src/dst 64))))

 (def-gl-export effects-copyData-loop-helper-9
   :hyp (and (< 4 m)
             (unsigned-byte-p 33 m))
   :concl (not (equal (loghead 64 (+ #xfffffffffffffffc m)) 0))
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes (:forward-chaining :rewrite))

 (def-gl-export effects-copyData-loop-helper-10
   :hyp (and (equal (loghead 64 (+ #xfffffffffffffffc m)) 0)
             (unsigned-byte-p 33 m))
   :concl (posp m)
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes (:forward-chaining))

 (def-gl-export loop-clk-measure-helper-alt
   :hyp (and (unsigned-byte-p 33 m)
             (<= 4 m))
   :concl (equal (< m (+ 4 (loghead 64 (+ #xfffffffffffffffc m)))) nil)
   :g-bindings (gl::auto-bindings (:int m 64)))

 (def-gl-export next-lower-bound-for-m
   :hyp (and (equal (mod m 4) 0)
             (< 4 m)
             (unsigned-byte-p 33 m))
   :concl (< 7 m)
   :g-bindings (gl::auto-bindings (:nat m 33))
   :rule-classes :forward-chaining)

 (local
  (def-gl-thm lower-bound-for-m-gl
    :hyp (and (equal (loghead 64 (+ #xfffffffffffffffc m)) 0)
              (equal (mod m 4) 0)
              (unsigned-byte-p 33 m))
    :concl (equal m 4)
    :g-bindings (gl::auto-bindings (:nat m 33))
    :rule-classes :forward-chaining))

 (defthm lower-bound-for-m
   (implies (and (equal (loghead 64 (+ #xfffffffffffffffc m)) 0)
                 (equal (mod m 4) 0)
                 (unsigned-byte-p 33 m))
            (equal m 4))
   :hints (("Goal" :in-theory (e/d* () (lower-bound-for-m-gl))
            :use ((:instance lower-bound-for-m-gl))))
   :rule-classes :forward-chaining)

 (def-gl-export effects-copyData-loop-helper-11
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (loghead 64 (+ #xfffffffffffffffc m))
                 (+ -4 m))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-12
   :hyp (and (< 4 m)
             (equal (mod m 4) 0)
             (unsigned-byte-p 33 m))
   :concl (equal (loghead 64 (+ #xfffffffffffffff8 m))
                 (+ -4 (loghead 64 (+ #xfffffffffffffffc m))))
   :g-bindings (gl::auto-bindings (:nat m 33)))

 (def-gl-export effects-copyData-loop-helper-13
   :hyp (and (equal (mod k 4) 0)
             (unsigned-byte-p 33 k))
   :concl (equal (mod (+ 4 k) 4) 0)
   :g-bindings (gl::auto-bindings (:nat k 33)))

 (in-theory (e/d () (effects-copyData-loop-helper-11
                     effects-copyData-loop-helper-12))))

;; ======================================================================

;; Here is the sub-routine:
;; void copyData (int* src, int* dst, int n) {

;;   int* dstEnd = dst + n;

;;   while (dst != dstEnd)
;;     *dst++ = *src++;

;; }

;; O1 optimization:
;; 0000000100000ed0 <_copyData>:
;;    100000ed0:	55                      push   %rbp
;;    100000ed1:	48 89 e5                mov    %rsp,%rbp
;;    100000ed4:	85 d2                   test   %edx,%edx
;;    100000ed6:	74 1a                   je     100000ef2 <_copyData+0x22>
;;    100000ed8:	48 63 c2                movslq %edx,%rax
;;    100000edb:	48 c1 e0 02             shl    $0x2,%rax
;;    100000edf:	90                      nop
;;    100000ee0:	8b 0f                   mov    (%rdi),%ecx
;;    100000ee2:	48 83 c7 04             add    $0x4,%rdi
;;    100000ee6:	89 0e                   mov    %ecx,(%rsi)
;;    100000ee8:	48 83 c6 04             add    $0x4,%rsi
;;    100000eec:	48 83 c0 fc             add    $0xfffffffffffffffc,%rax
;;    100000ef0:	75 ee                   jne    100000ee0 <_copyData+0x10>
;;    100000ef2:	5d                      pop    %rbp
;;    100000ef3:	c3                      retq

(defconst *copyData* ;; 15 instructions
  '(
    #x55           ;; push   %rbp                          1
    #x48 #x89 #xe5 ;; mov    %rsp,%rbp			2
    #x85 #xd2      ;; test   %edx,%edx			3
    #x74 #x1a      ;; je     100000ef2 <_copyData+0x22>	4   (jump if ZF = 1)
    #x48 #x63 #xc2 ;; movslq %edx,%rax			5
    #x48 #xc1 #xe0 #x02 ;; shl    $0x2,%rax			6
    #x90                ;; nop                                  7
    #x8b #x0f           ;; mov    (%rdi),%ecx			8
    #x48 #x83 #xc7 #x04 ;; add    $0x4,%rdi			9
    #x89 #x0e           ;; mov    %ecx,(%rsi)                  10
    #x48 #x83 #xc6 #x04 ;; add    $0x4,%rsi                    11
    #x48 #x83 #xc0 #xfc ;; add    $0xfffffffffffffffc,%rax     12
    #x75 #xee ;; jne    100000ee0 <_copyData+0x10>   13   (jump if ZF = 0)
    #x5d      ;; pop    %rbp                         14
    #xc3      ;; retq                                15
    ))

;; Some important registers:

;; RDX: n
;; RSI: Destination address
;; RDI: Source address

;; ======================================================================

(local (in-theory (e/d* (rb-rb-subset) ())))

;; ======================================================================

(defun-nx source-bytes (k src-addr x86)
  (mv-nth 1 (rb (create-canonical-address-list k (+ (- k) src-addr))
                :x x86)))

(defun-nx destination-bytes (k dst-addr x86)
  (mv-nth 1 (rb (create-canonical-address-list k (+ (- k) dst-addr))
                :x x86)))

(defun-nx loop-invariant (k m addr x86)
  ;; The initial value of m is (ash n 2), where n is the same n as defined in
  ;; preconditions.

  ;; k: number of bytes already copied (in previous loop iterations)
  ;;    this will increase by 4 in every iteration
  ;; m: number of bytes to be copied
  ;;    this will decrease by 4 in every iteration

  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       (unsigned-byte-p 33 m)
       (equal (mod m 4) 0)
       (unsigned-byte-p 33 k)
       (equal (mod k 4) 0)
       (unsigned-byte-p 33 (+ m k))
       (equal (xr :rgf *rax* x86) m)
       ;; Stack address is canonical.
       (canonical-address-p (xr :rgf *rsp* x86))
       ;; All the destination addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
       (canonical-address-p (+ m (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
       (canonical-address-p (+ m (xr :rgf *rdi* x86)))
       ;; Memory locations of interest are disjoint.
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Destination addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rdi* x86)))
        ;; Destination Addresses
        (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ -1 (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)
       ;; Values copied in the previous iterations of the loop are unaltered.
       ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
       (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
              (source-bytes      k (xr :rgf *rdi* x86) x86))))

(defun-nx loop-preconditions (k m addr src-addr dst-addr x86)
  (and (loop-invariant k m addr x86)
       ;; At the beginning of every iteration, we have some bytes left to be
       ;; copied.
       (posp m)
       (equal (xr :rgf *rdi* x86) src-addr)
       (equal (xr :rgf *rsi* x86) dst-addr)
       (equal addr (+ -16 (xr :rip 0 x86)))))

(defthm loop-preconditions-fwd-chain-to-its-body
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                (unsigned-byte-p 33 m)
                (equal (mod m 4) 0)
                (unsigned-byte-p 33 k)
                (equal (mod k 4) 0)
                (unsigned-byte-p 33 (+ m k))
                (equal (xr :rgf *rax* x86) m)
                ;; Stack address is canonical.
                (canonical-address-p (xr :rgf *rsp* x86))
                ;; All the destination addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
                (canonical-address-p (+ m (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
                (canonical-address-p (+ m (xr :rgf *rdi* x86)))
                ;; Memory locations of interest are disjoint.
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Destination addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rdi* x86)))
                 ;; Destination Addresses
                 (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ -1 (len *copyData*) addr))
                (program-at (create-canonical-address-list (len *copyData*) addr)
                            *copyData* x86)
                ;; Values copied in the previous iterations of the loop are unaltered.
                ;; dst[(+ -k dst-addr) to dst-addr]  =  src[(+ -k src-addr) to src-addr]
                (equal (destination-bytes k (xr :rgf *rsi* x86) x86)
                       (source-bytes      k (xr :rgf *rdi* x86) x86))
                (posp m)
                (equal (xr :rgf *rdi* x86) src-addr)
                (equal (xr :rgf *rsi* x86) dst-addr)
                (equal addr (+ -16 (xr :rip 0 x86)))))
  :rule-classes :forward-chaining)

;; ======================================================================

;; Clock functions:

(defun pre-clk (n)
  (if (zp n) 4 7))

(defun loop-clk-base () 6)
(defun loop-clk-recur () 6)

(defun loop-clk (m)
  ;; I use m to refer to (ash n 2).
  (if (signed-byte-p 64 m)
      (let ((new-m (loghead 64 (+ #xfffffffffffffffc m))))
        (if (<= m 4)
            (loop-clk-base)
          (clk+ (loop-clk-recur) (loop-clk new-m))))
    0))

(defun post-clk () 2)

(defun clk (n)
  (if (zp n)
      (pre-clk n)
    (clk+ (pre-clk n)
          (loop-clk (ash n 2)))))

(defun program-clk (n)
  (clk+ (clk n) (post-clk)))

;; ======================================================================

;; Some useful arithmetic theorems:

(defthm greater-logbitp-of-unsigned-byte-p
  ;; From word-count/wc.lisp
  (implies (and (unsigned-byte-p n x)
                (natp m)
                (< n m))
           (equal (logbitp m x) nil))
  :hints (("Goal" :in-theory (e/d* (ihsext-inductions
                                    ihsext-recursive-redefs
                                    unsigned-byte-p)
                                   ())))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary
                           (implies (and (< x (expt 2 m))
                                         (natp x)
                                         (natp m))
                                    (equal (logbitp m x) nil)))))

(encapsulate
 ()

 (local (include-book "arithmetic-3/top" :dir :system))

 (defthm ash-n-2-bound
   (implies (and (< 0 n)
                 (integerp n))
            (<= 4 (ash n 2)))
   :hints (("Goal" :in-theory (e/d* (ash) ())))
   :rule-classes (:rewrite :linear)))

;; [Shilpi]: These two rules below show how canonical-address-p-limits-thm-0,
;; canonical-address-p-limits-thm-1, and canonical-address-p-limits-thm-2 break
;; down when i, j, and k aren't simple terms, like constants.

(defthm canonical-address-p-and-ash-limits-thm-1
  (implies (and (canonical-address-p (+ x (ash n 2)))
                (canonical-address-p x)
                (posp n))
           (canonical-address-p (+ -1 (+ x (ash n 2)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ()))))

(defthm canonical-address-p-and-ash-limits-thm-2
  (implies (and (canonical-address-p (+ x (ash n 2)))
                (< m (ash n 2))
                (canonical-address-p x)
                (natp m))
           (canonical-address-p (+ m x)))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ()))))

;; [Shilpi]: This rule below shows how disjoint-p-subset-p and
;; subset-p-two-create-canonical-address-lists break down because subset-p
;; can't be established.

(defthm subset-p-ash-thm-1
  (implies (and (<= m (ash n 2))
                (unsigned-byte-p 31 n)
                (canonical-address-p x)
                (canonical-address-p (+ (ash n 2) x))
                (< 0 n))
           (subset-p (create-canonical-address-list m x)
                     (create-canonical-address-list (ash n 2) x))))

;; ======================================================================

;; Effects theorem:

(defthm subset-p-linear-thm-1
  (implies (and (canonical-address-p (+ m x))
                (natp m)
                (<= i m))
           (subset-p (create-canonical-address-list i x)
                     (create-canonical-address-list m x)))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(encapsulate
 ()

 (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

 (defthm mod-thm-1
   (implies (and (equal (mod m 4) 0)
                 (posp m))
            (<= 4 m))
   :rule-classes (:forward-chaining)))

(defthm canonical-address-p-of-src/dst
  (implies (and (canonical-address-p (+ (- k) src/dst))
                (canonical-address-p (+ m src/dst))
                (integerp src/dst)
                (natp k)
                (natp m))
           (canonical-address-p src/dst))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:rewrite :forward-chaining))

(defthmd effects-copyData-loop-base
  (implies
   (and (equal m 4)
        (loop-preconditions k m addr src-addr dst-addr x86))
   (equal (x86-run (loop-clk-base) x86)
          (XW
           :RGF *RAX* 0
           (XW
            :RGF *RCX*
            (COMBINE-BYTES
             (MV-NTH 1
                     (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                         :X X86)))
            (XW
             :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
             (XW
              :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
              (XW
               :RIP 0 (+ 18 (XR :RIP 0 X86))
               (MV-NTH
                1
                (WB
                 (CREATE-ADDR-BYTES-ALIST
                  (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RSI* X86))
                  (BYTE-IFY
                   4
                   (COMBINE-BYTES
                    (MV-NTH 1
                            (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                :X X86)))))
                 (WRITE-USER-RFLAGS
                  (LOGIOR
                   (LOGHEAD 32
                            (CF-SPEC64 (+ #xfffffffffffffffc
                                          (XR :RGF *RAX* X86))))
                   (LOGHEAD 32
                            (ASH (PF-SPEC64 (LOGHEAD 64
                                                     (+ #xfffffffffffffffc
                                                        (XR :RGF *RAX* X86))))
                                 2))
                   (LOGAND
                    4294967290
                    (LOGIOR
                     (LOGHEAD 32
                              (ASH (ADD-AF-SPEC64 (XR :RGF *RAX* X86)
                                                  #xfffffffffffffffc)
                                   4))
                     (LOGAND
                      4294967278
                      (LOGIOR
                       (LOGHEAD 32
                                (ASH (ZF-SPEC (LOGHEAD 64
                                                       (+ #xfffffffffffffffc
                                                          (XR :RGF *RAX* X86))))
                                     6))
                       (LOGAND
                        4294967230
                        (LOGIOR
                         (LOGHEAD 32
                                  (ASH (SF-SPEC64 (LOGHEAD 64
                                                           (+ #xfffffffffffffffc
                                                              (XR :RGF *RAX* X86))))
                                       7))
                         (LOGAND
                          4294967166
                          (LOGIOR
                           (LOGHEAD 32
                                    (ASH (OF-SPEC64 (+ -4 (XR :RGF *RAX* X86)))
                                         11))
                           (LOGAND
                            4294965246
                            (LOGIOR
                             (BITOPS::LOGSQUASH
                              1
                              (LOGHEAD
                               32
                               (CF-SPEC64 (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86))))))
                             (BITOPS::LOGSQUASH
                              1
                              (LOGHEAD
                               32
                               (ASH
                                (PF-SPEC64
                                 (LOGHEAD 64
                                          (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                2)))
                             (LOGAND
                              4294967290
                              (LOGIOR
                               (BITOPS::LOGSQUASH
                                1
                                (LOGHEAD
                                 32
                                 (ASH (ADD-AF-SPEC64 (LOGHEAD 64 (XR :RGF *RSI* X86))
                                                     4)
                                      4)))
                               (LOGAND
                                4294967278
                                (LOGIOR
                                 (BITOPS::LOGSQUASH
                                  1
                                  (LOGHEAD
                                   32
                                   (ASH
                                    (ZF-SPEC
                                     (LOGHEAD
                                      64
                                      (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                    6)))
                                 (LOGAND
                                  4294967230
                                  (LOGIOR
                                   (BITOPS::LOGSQUASH
                                    1
                                    (LOGHEAD
                                     32
                                     (ASH
                                      (SF-SPEC64
                                       (LOGHEAD
                                        64
                                        (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                      7)))
                                   (LOGAND
                                    4294967166
                                    (LOGIOR
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (ASH (OF-SPEC64 (+ 4 (XR :RGF *RSI* X86)))
                                            11)))
                                     (LOGAND
                                      4294965246
                                      (LOGIOR
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (CF-SPEC64
                                          (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86))))))
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (ASH
                                          (PF-SPEC64
                                           (LOGHEAD
                                            64
                                            (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                          2)))
                                       (LOGAND
                                        4294967290
                                        (LOGIOR
                                         (BITOPS::LOGSQUASH
                                          1
                                          (LOGHEAD
                                           32
                                           (ASH (ADD-AF-SPEC64
                                                 (LOGHEAD 64 (XR :RGF *RDI* X86))
                                                 4)
                                                4)))
                                         (LOGAND
                                          4294967278
                                          (LOGIOR
                                           (BITOPS::LOGSQUASH
                                            1
                                            (LOGHEAD
                                             32
                                             (ASH
                                              (ZF-SPEC
                                               (LOGHEAD
                                                64
                                                (+
                                                 4
                                                 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                              6)))
                                           (LOGAND
                                            4294967230
                                            (LOGIOR
                                             (BITOPS::LOGSQUASH
                                              1
                                              (LOGHEAD
                                               32
                                               (ASH
                                                (SF-SPEC64
                                                 (LOGHEAD
                                                  64
                                                  (+ 4
                                                     (LOGHEAD
                                                      64 (XR :RGF *RDI* X86)))))
                                                7)))
                                             (LOGAND
                                              4294967166
                                              (LOGIOR
                                               (LOGAND 4294965246
                                                       (BITOPS::LOGSQUASH
                                                        1 (XR :RFLAGS 0 X86)))
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (ASH
                                                  (OF-SPEC64
                                                   (+ 4 (XR :RGF *RDI* X86)))
                                                  11))))))))))))))))))))))))))))))))
                  0 X86))))))))))
  :hints (("Goal"
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

                             opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             signed-byte-p)
                            (wb-remove-duplicate-writes
                             create-canonical-address-list)))))

(defthm effects-copyData-loop-base-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-base) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-base) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-destination-address-projection
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-base) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-base) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base)
                        (:instance effects-copyData-loop-base-destination-address-projection-copied)
                        (:instance effects-copyData-loop-base-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86)))
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-base) x86))))
           :in-theory (e/d* ()
                            (loop-clk-base
                             effects-copyData-loop-base-destination-address-projection-copied
                             effects-copyData-loop-base-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-programmer-level-mode-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :programmer-level-mode 0 (x86-run (loop-clk-base) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-base) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-base) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rax-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rgf *rax* (x86-run (loop-clk-base) x86))
                  0))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (equal prog-len (len *copydata*))
                (<= m 4))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (loop-clk-base) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :fault 0 (x86-run (loop-clk-base) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :ms 0 (x86-run (loop-clk-base) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthm effects-copyData-loop-base-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (<= m 4))
           (equal (xr :rip 0 (x86-run (loop-clk-base) x86))
                  (+ 18 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-loop-base))
           :in-theory (e/d* ()
                            (loop-clk-base
                             (loop-clk-base)
                             force (force))))))

(defthmd canonical-address-p-and-ash-limits-thm-3
  ;; [Shilpi]: Very similar to canonical-address-p-and-ash-limits-thm-1. Think
  ;; about eliminating that rule?
  (implies (and (canonical-address-p (+ m x))
                (canonical-address-p x)
                (posp m))
           (canonical-address-p (+ -1 (+ m x))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ())))
  :rule-classes (:forward-chaining :rewrite))

(defthmd disjointness-lemma-1-helper
  (implies (and (x86p x86)
                (unsigned-byte-p 33 k)
                (equal (xr :rgf *rax* x86) m)
                (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
                (canonical-address-p (+ m (xr :rgf *rsi* x86)))
                (< 4 m))
           (subset-p (create-canonical-address-list 4 (xr :rgf *rsi* x86))
                     (create-canonical-address-list (+ k m) (+ (- k) (xr :rgf *rsi* x86)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p-and-ash-limits-thm-3 subset-p) ())
           :do-not-induct t)))

(defthm disjointness-lemma-1
  (implies (and
            (x86p x86)
            (equal (mod m 4) 0)
            (unsigned-byte-p 33 k)
            (equal (xr :rgf *rax* x86) m)
            (canonical-address-p (+ (- k) (xr :rgf *rsi* x86)))
            (canonical-address-p (+ m (xr :rgf *rsi* x86)))
            (disjoint-p
             (create-canonical-address-list (len *copydata*) addr)
             (create-canonical-address-list (+ m k) (+ (- k) (xr :rgf *rsi* x86))))
            (posp m)
            (equal addr (+ -16 (xr :rip 0 x86))))
           (disjoint-p (create-canonical-address-list 36 (+ -16 (xr :rip 0 x86)))
                       (create-canonical-address-list 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance disjointness-lemma-1-helper)))))

(defthmd effects-copyData-loop-recur
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (x86-run (loop-clk-recur) x86)
                  (XW
                   :RGF *RAX*
                   (LOGHEAD 64
                            (+ #xfffffffffffffffc
                               (XR :RGF *RAX* X86)))
                   (XW
                    :RGF *RCX*
                    (COMBINE-BYTES
                     (MV-NTH 1
                             (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                 :X X86)))
                    (XW
                     :RGF *RSI* (+ 4 (XR :RGF *RSI* X86))
                     (XW
                      :RGF *RDI* (+ 4 (XR :RGF *RDI* X86))
                      (XW
                       :RIP 0 (XR :RIP 0 X86)
                       (MV-NTH
                        1
                        (WB
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RSI* X86))
                          (BYTE-IFY
                           4
                           (COMBINE-BYTES
                            (MV-NTH 1
                                    (RB (CREATE-CANONICAL-ADDRESS-LIST 4 (XR :RGF *RDI* X86))
                                        :X X86)))))
                         (WRITE-USER-RFLAGS
                          (LOGIOR
                           (LOGHEAD 32
                                    (CF-SPEC64 (+ #xfffffffffffffffc
                                                  (XR :RGF *RAX* X86))))
                           (LOGHEAD 32
                                    (ASH (PF-SPEC64 (LOGHEAD 64
                                                             (+ #xfffffffffffffffc
                                                                (XR :RGF *RAX* X86))))
                                         2))
                           (LOGAND
                            4294967290
                            (LOGIOR
                             (LOGHEAD 32
                                      (ASH (ADD-AF-SPEC64 (XR :RGF *RAX* X86)
                                                          #xfffffffffffffffc)
                                           4))
                             (LOGAND
                              4294967278
                              (LOGIOR
                               (LOGHEAD 32
                                        (ASH (ZF-SPEC (LOGHEAD 64
                                                               (+ #xfffffffffffffffc
                                                                  (XR :RGF *RAX* X86))))
                                             6))
                               (LOGAND
                                4294967230
                                (LOGIOR
                                 (LOGHEAD 32
                                          (ASH (SF-SPEC64 (LOGHEAD 64
                                                                   (+ #xfffffffffffffffc
                                                                      (XR :RGF *RAX* X86))))
                                               7))
                                 (LOGAND
                                  4294967166
                                  (LOGIOR
                                   (LOGHEAD 32
                                            (ASH (OF-SPEC64 (+ -4 (XR :RGF *RAX* X86)))
                                                 11))
                                   (LOGAND
                                    4294965246
                                    (LOGIOR
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (CF-SPEC64 (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86))))))
                                     (BITOPS::LOGSQUASH
                                      1
                                      (LOGHEAD
                                       32
                                       (ASH
                                        (PF-SPEC64
                                         (LOGHEAD 64
                                                  (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                        2)))
                                     (LOGAND
                                      4294967290
                                      (LOGIOR
                                       (BITOPS::LOGSQUASH
                                        1
                                        (LOGHEAD
                                         32
                                         (ASH (ADD-AF-SPEC64 (LOGHEAD 64 (XR :RGF *RSI* X86))
                                                             4)
                                              4)))
                                       (LOGAND
                                        4294967278
                                        (LOGIOR
                                         (BITOPS::LOGSQUASH
                                          1
                                          (LOGHEAD
                                           32
                                           (ASH
                                            (ZF-SPEC
                                             (LOGHEAD
                                              64
                                              (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                            6)))
                                         (LOGAND
                                          4294967230
                                          (LOGIOR
                                           (BITOPS::LOGSQUASH
                                            1
                                            (LOGHEAD
                                             32
                                             (ASH
                                              (SF-SPEC64
                                               (LOGHEAD
                                                64
                                                (+ 4 (LOGHEAD 64 (XR :RGF *RSI* X86)))))
                                              7)))
                                           (LOGAND
                                            4294967166
                                            (LOGIOR
                                             (BITOPS::LOGSQUASH
                                              1
                                              (LOGHEAD
                                               32
                                               (ASH (OF-SPEC64 (+ 4 (XR :RGF *RSI* X86)))
                                                    11)))
                                             (LOGAND
                                              4294965246
                                              (LOGIOR
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (CF-SPEC64
                                                  (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86))))))
                                               (BITOPS::LOGSQUASH
                                                1
                                                (LOGHEAD
                                                 32
                                                 (ASH
                                                  (PF-SPEC64
                                                   (LOGHEAD
                                                    64
                                                    (+ 4 (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                                  2)))
                                               (LOGAND
                                                4294967290
                                                (LOGIOR
                                                 (BITOPS::LOGSQUASH
                                                  1
                                                  (LOGHEAD
                                                   32
                                                   (ASH (ADD-AF-SPEC64
                                                         (LOGHEAD 64 (XR :RGF *RDI* X86))
                                                         4)
                                                        4)))
                                                 (LOGAND
                                                  4294967278
                                                  (LOGIOR
                                                   (BITOPS::LOGSQUASH
                                                    1
                                                    (LOGHEAD
                                                     32
                                                     (ASH
                                                      (ZF-SPEC
                                                       (LOGHEAD
                                                        64
                                                        (+
                                                         4
                                                         (LOGHEAD 64 (XR :RGF *RDI* X86)))))
                                                      6)))
                                                   (LOGAND
                                                    4294967230
                                                    (LOGIOR
                                                     (BITOPS::LOGSQUASH
                                                      1
                                                      (LOGHEAD
                                                       32
                                                       (ASH
                                                        (SF-SPEC64
                                                         (LOGHEAD
                                                          64
                                                          (+ 4
                                                             (LOGHEAD
                                                              64 (XR :RGF *RDI* X86)))))
                                                        7)))
                                                     (LOGAND
                                                      4294967166
                                                      (LOGIOR
                                                       (LOGAND 4294965246
                                                               (BITOPS::LOGSQUASH
                                                                1 (XR :RFLAGS 0 X86)))
                                                       (BITOPS::LOGSQUASH
                                                        1
                                                        (LOGHEAD
                                                         32
                                                         (ASH
                                                          (OF-SPEC64
                                                           (+ 4 (XR :RGF *RDI* X86)))
                                                          11))))))))))))))))))))))))))))))))
                          0 X86))))))))))
  :hints (("Goal"
           :use ((:instance disjointness-lemma-1))
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

                             opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             signed-byte-p)
                            (wb-remove-duplicate-writes
                             disjointness-lemma-1
                             create-canonical-address-list)))))

(defthm effects-copyData-loop-recur-destination-address-projection-original
  ;; dst[(+ -k dst-addr) to dst-addr] in (x86-run (loop-clk-recur) x86) =
  ;; dst[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes k dst-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k dst-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection-copied
  ;; dst[(dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes 4 (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-destination-address-projection
  ;; dst[(+ -k dst-addr) to (dst-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (destination-bytes (+ 4 k) (+ 4 dst-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-destination-address-projection-copied)
                        (:instance effects-copyData-loop-recur-destination-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rsi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-destination-address-projection-copied
                             effects-copyData-loop-recur-destination-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthmd disjointness-lemma-2
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (disjoint-p (create-canonical-address-list k (+ (- k) (xr :rgf *rdi* x86)))
                       (create-canonical-address-list 4 (xr :rgf *rsi* x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjointness-lemma-1-helper) ()))))

(defthm effects-copyData-loop-recur-source-address-projection-original
  ;; src[(+ -k src-addr) to src-addr] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to src-addr] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes k src-addr (x86-run (loop-clk-recur) x86))
                  (source-bytes k src-addr x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance disjointness-lemma-2))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthmd disjointness-lemma-3-helper
  (implies (and (x86p x86)
                (unsigned-byte-p 33 k)
                (equal (xr :rgf *rax* x86) m)
                (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
                (canonical-address-p (+ m (xr :rgf *rdi* x86)))
                (< 4 m))
           (subset-p (create-canonical-address-list 4 (xr :rgf *rdi* x86))
                     (create-canonical-address-list (+ k m) (+ (- k) (xr :rgf *rdi* x86)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p-and-ash-limits-thm-3 subset-p) ())
           :do-not-induct t)))

(defthmd disjointness-lemma-3
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (disjoint-p (create-canonical-address-list 4 (xr :rgf *rdi* x86))
                       (create-canonical-address-list 4 (xr :rgf *rsi* x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjointness-lemma-1-helper
                             disjointness-lemma-3-helper) ()))))

(defthm effects-copyData-loop-recur-source-address-projection-copied
  ;; src[(src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes 4 (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes 4 (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance disjointness-lemma-3))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection
  ;; src[(+ -k src-addr) to (src-addr + 4)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + 4)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ 4 k) (+ 4 src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ 4 k) (+ 4 src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-source-address-projection-copied)
                        (:instance effects-copyData-loop-recur-source-address-projection-original)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j 4)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j 4)
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-programmer-level-mode-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :programmer-level-mode 0 (x86-run (loop-clk-recur) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-ms-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :ms 0 (x86-run (loop-clk-recur) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-fault-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :fault 0 (x86-run (loop-clk-recur) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-program-at-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (loop-clk-recur) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur)
                 (:instance disjointness-lemma-1))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             disjointness-lemma-1
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsp-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsp* (x86-run (loop-clk-recur) x86))
                  (xr :rgf *rsp* x86)))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rsi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rsi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rsi* x86))))
  :hints (("Goal" :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rdi-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rdi* (x86-run (loop-clk-recur) x86))
                  (+ 4 (xr :rgf *rdi* x86))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rax-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rgf *rax* (x86-run (loop-clk-recur) x86))
                  (loghead 64 (+ #xfffffffffffffffc (xr :rgf *rax* x86)))))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-rip-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (xr :rip 0 (x86-run (loop-clk-recur) x86))
                  (xr :rip 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop-recur))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-x86p-projection
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (x86p (x86-run (loop-clk-recur) x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (loop-clk-recur
                                    (loop-clk-recur)
                                    force (force))))))

(defthm effects-copyData-loop-recur-implies-loop-preconditions
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (loop-preconditions (+ 4 k)
                               (loghead 64 (+ #xfffffffffffffffc m))
                               addr (+ 4 src-addr)
                               (+ 4 dst-addr)
                               (x86-run (loop-clk-recur) x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance loop-preconditions-fwd-chain-to-its-body))
           :expand (loop-preconditions (+ 4 k)
                                       (loghead 64 (+ #xfffffffffffffffc (xr :rgf *rax* x86)))
                                       (+ -16 (xr :rip 0 x86))
                                       (+ 4 (xr :rgf *rdi* x86))
                                       (+ 4 (xr :rgf *rsi* x86))
                                       (x86-run (loop-clk-recur) x86))
           :in-theory (e/d* (unsigned-byte-p)
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             destination-bytes
                             source-bytes
                             loop-preconditions
                             loop-preconditions-fwd-chain-to-its-body
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :in-theory (e/d* (effects-copyData-loop-helper-11)
                                        ()))))


(defthm x86p-state-after-loop-clk-base
  (implies (x86p x86)
           (x86p (x86-run (loop-clk-base) x86))))

(defthm x86p-state-after-loop-clk-recur
  (implies (x86p x86)
           (x86p (x86-run (loop-clk-recur) x86))))

(defun-nx loop-state (k m src-addr dst-addr x86)

  (if (signed-byte-p 64 m) ;; This should always be true.

      (if (<= m 4)

          (x86-run (loop-clk-base) x86)

        (b* ((new-m (loghead 64 (+ #xfffffffffffffffc m)))
             (new-k (+ 4 k))
             (new-src-addr (+ 4 src-addr))
             (new-dst-addr (+ 4 dst-addr))
             (x86 (x86-run (loop-clk-recur) x86)))
            (loop-state new-k new-m new-src-addr new-dst-addr x86)))
    x86))

(defthm x86p-loop-state
  (implies (x86p x86)
           (x86p (loop-state k m src-addr dst-addr x86)))
  :hints (("Goal" :in-theory (e/d* () ()))))

(defthmd x86-run-plus-for-loop-clk-recur-1
  (equal (x86-run (loop-clk (loghead 64 (+ #xfffffffffffffffc m)))
                  (x86-run (loop-clk-recur) x86))
         (x86-run (binary-clk+ (loop-clk-recur)
                               (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                  x86))
  :hints (("Goal" :in-theory (e/d* () (x86-run-plus (loop-clk-recur) loop-clk-recur))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk (loghead 64 (+ #xfffffffffffffffc m))))
                            (n1 (loop-clk-recur)))))))

(defthmd x86-run-plus-for-loop-clk-recur-2
  (equal (x86-run (binary-clk+ (loop-clk-recur) (loop-clk-base)) x86)
         (x86-run (loop-clk-base) (x86-run (loop-clk-recur) x86)))
  :hints (("Goal" :in-theory (e/d* () (x86-run-plus (loop-clk-recur) loop-clk-recur loop-clk-base (loop-clk-base)))
           :use ((:instance x86-run-plus
                            (n2 (loop-clk-base))
                            (n1 (loop-clk-recur)))))))

(defthm effects-copyData-loop
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (equal (x86-run (loop-clk m) x86)
                  (loop-state k m src-addr dst-addr x86)))
  :hints (("Goal"
           :induct (cons (loop-state k m src-addr dst-addr x86) (loop-clk m))
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             gpr-and-spec-4
                             gpr-add-spec-8
                             jcc/cmovcc/setcc-spec
                             sal/shl-spec
                             sal/shl-spec-64

                             opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr64
                             wr32
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             subset-p
                             signed-byte-p

                             x86-run-plus-for-loop-clk-recur-1
                             x86-run-plus-for-loop-clk-recur-2)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             ;; [Shilpi]: Note that the executable-counterpart
                             ;; of loop-clk needs to be disabled, else
                             ;; (loop-clk-base) will be rewritten to 6,
                             ;; irrespective of whether loop-clk-base is
                             ;; completely disabled.
                             (loop-clk)
                             loop-preconditions
                             wb-remove-duplicate-writes
                             create-canonical-address-list
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             force (force))))))

(defthmd pull-out-loop-clk-recur-from-loop-state-helper
  (equal (x86-run (loop-clk-base)
                  (x86-run (loop-clk-recur) x86))
         (x86-run (loop-clk-recur)
                  (x86-run (loop-clk-base) x86))))

(defthmd pull-out-loop-clk-recur-from-loop-state
  (implies (and (bind-free '((addr . addr)))
                (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (loop-state k m src-addr dst-addr x86)
                  (x86-run (loop-clk-recur)
                           (loop-state (+ 4 k)
                                       (+ -4 m)
                                       (+ 4 src-addr)
                                       (+ 4 dst-addr)
                                       x86))))
  :hints (("Goal"
           :in-theory (e/d* (pull-out-loop-clk-recur-from-loop-state-helper
                             effects-copyData-loop-helper-11)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             (loop-clk)
                             loop-preconditions
                             wb-remove-duplicate-writes
                             create-canonical-address-list
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             effects-copyData-loop-recur-implies-loop-preconditions
                             force (force))))
          ("Subgoal *1/1"
           :use ((:instance effects-copyData-loop-recur-implies-loop-preconditions))
           :in-theory (e/d* (pull-out-loop-clk-recur-from-loop-state-helper
                             effects-copyData-loop-helper-11)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             (loop-clk)
                             loop-preconditions
                             wb-remove-duplicate-writes
                             create-canonical-address-list
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             effects-copyData-loop-recur-implies-loop-preconditions
                             force (force))))
          ("Subgoal *1/3"
           :expand (loop-state (+ 4 k) (+ -4 m) (+ 4 src-addr) (+ 4 dst-addr) x86)
           :in-theory (e/d* (pull-out-loop-clk-recur-from-loop-state-helper
                             effects-copyData-loop-helper-12)
                            (loop-clk-base
                             (loop-clk-base)
                             (:type-prescription loop-clk-base)
                             loop-clk-recur
                             (loop-clk-recur)
                             (:type-prescription loop-clk-recur)
                             (loop-clk)
                             loop-preconditions
                             wb-remove-duplicate-writes
                             create-canonical-address-list
                             effects-copyData-loop-recur
                             effects-copyData-loop-base
                             effects-copyData-loop-recur-implies-loop-preconditions
                             force (force))))))


(defthm programmer-level-mode-of-loop-state
  (implies (loop-preconditions k m addr src-addr dst-addr x86)
           (xr :programmer-level-mode 0 (loop-state k m src-addr dst-addr x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthmd disjointness-lemma-4-helper
  (implies (and (x86p x86)
                (unsigned-byte-p 33 k)
                (equal (xr :rgf *rax* x86) m)
                (canonical-address-p (+ (- k) (xr :rgf *rdi* x86)))
                (canonical-address-p (+ m (xr :rgf *rdi* x86)))
                (< 4 m))
           (subset-p (create-canonical-address-list m (xr :rgf *rdi* x86))
                     (create-canonical-address-list (+ k m) (+ (- k) (xr :rgf *rdi* x86)))))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p-and-ash-limits-thm-3 subset-p) ())
           :do-not-induct t)))

(defthmd disjointness-lemma-4
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (disjoint-p (create-canonical-address-list m (xr :rgf *rdi* x86))
                       (create-canonical-address-list 4 (xr :rgf *rsi* x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjointness-lemma-1-helper
                             disjointness-lemma-3-helper
                             disjointness-lemma-4-helper)
                            ()))))


(defthm effects-copyData-loop-recur-source-address-projection-full-helper
  ;; src[src-addr to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[src-addr to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes m (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance disjointness-lemma-4))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthm effects-copyData-loop-recur-source-address-projection-full
  ;; src[(+ -k src-addr) to (src-addr + m)] in (x86-run (loop-clk-recur) x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (< 4 m))
           (equal (source-bytes (+ m k) (+ m src-addr) (x86-run (loop-clk-recur) x86))
                  (source-bytes (+ m k) (+ m src-addr) x86)))
  :hints (("Goal" :use ((:instance effects-copydata-loop-recur)
                        (:instance effects-copyData-loop-recur-source-address-projection-copied)
                        (:instance effects-copyData-loop-recur-source-address-projection-original)
                        (:instance effects-copyData-loop-recur-source-address-projection-full-helper)
                        (:instance rb-rb-split-reads
                                   (k k)
                                   (j m)
                                   (r-w-x :x)
                                   (addr (+ (- k) (xr :rgf *rdi* x86)))
                                   (x86 (x86-run (loop-clk-recur) x86))))
           :in-theory (e/d* ()
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-full-helper
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))
          ("Subgoal 1" :use ((:instance rb-rb-split-reads
                                        (k k)
                                        (j (xr :rgf *rax* x86))
                                        (r-w-x :x)
                                        (addr (+ (- k) (xr :rgf *rdi* x86)))
                                        (x86 x86)))
           :in-theory (e/d* (unsigned-byte-p)
                            (loop-clk-recur
                             effects-copyData-loop-recur-source-address-projection-copied
                             effects-copyData-loop-recur-source-address-projection-original
                             rb-rb-split-reads
                             take-and-rb
                             acl2::take-of-append
                             (loop-clk-recur)
                             force (force))))))

(defthmd destination-array-and-loop-state
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (loop-state k m src-addr dst-addr x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-preconditions
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))
          ("Subgoal *1/3"
           :use ((:instance effects-copyData-loop-recur-source-address-projection-full))
           :hands-off (x86-run)
           :in-theory (e/d* (effects-copyData-loop-helper-11)
                            (loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             create-canonical-address-list)))))

(defthm destination-array-and-x86-state-after-loop-clk
  ;; dst[(+ -k dst-addr) to (dst-addr + m)] in (loop-state k m src-addr dst-addr x86) =
  ;; src[(+ -k src-addr) to (src-addr + m)] in x86
  (implies (and (loop-preconditions k m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes (+ k m) (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes (+ k m) (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance effects-copyData-loop)
                 (:instance destination-array-and-loop-state))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (effects-copyData-loop
                             loop-preconditions
                             effects-copyData-loop-recur-source-address-projection-full
                             loop-invariant
                             destination-bytes
                             source-bytes
                             loop-clk-recur
                             (loop-clk-recur)
                             loop-clk-base
                             (loop-clk-base)
                             loop-clk
                             (loop-clk)
                             create-canonical-address-list)))))

(defthm loop-copies-m-bytes-from-source-to-destination
  ;; dst[ dst-addr to (dst-addr + m) ] in (loop-state 0 m src-addr dst-addr x86) =
  ;; src[ src-addr to (src-addr + m) ] in x86
  (implies (and (loop-preconditions 0 m addr src-addr dst-addr x86)
                (natp k))
           (equal (destination-bytes m (+ m dst-addr) (x86-run (loop-clk m) x86))
                  (source-bytes m (+ m src-addr) x86)))
  :hints (("Goal"
           :use ((:instance destination-array-and-x86-state-after-loop-clk
                            (k 0)))
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (loop-clk-recur
                             destination-array-and-loop-state
                             (loop-clk-recur)
                             loop-clk-base
                             destination-bytes
                             source-bytes
                             (loop-clk-base)
                             loop-preconditions
                             effects-copyData-loop
                             effects-copyData-loop-base
                             effects-copyData-loop-recur
                             force (force))))))

;; ======================================================================

(defun-nx preconditions (n addr x86)
  (and (x86p x86)
       (xr :programmer-level-mode 0 x86)
       (equal (xr :ms 0 x86) nil)
       (equal (xr :fault 0 x86) nil)
       ;; We are poised to run the copyData sub-routine.
       (equal (xr :rip 0 x86) addr)
       (unsigned-byte-p 31 n)
       (equal (xr :rgf *rdx* x86) n)
       ;; All the stack addresses are canonical.
       (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
       (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
       ;; All the destination addresses are canonical.
       (canonical-address-p (xr :rgf *rsi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
       ;; All the source addresses are canonical.
       (canonical-address-p (xr :rgf *rdi* x86))
       (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
       ;; Memory locations of interest are disjoint.
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Destination addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       (disjoint-p
        ;; Program addresses
        (create-canonical-address-list (len *copyData*) addr)
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86))
        ;; Stack
        (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
       (disjoint-p
        ;; Source Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
        ;; Destination Addresses
        (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
       ;; Program is located at addr.
       ;; All program addresses are canonical.
       (canonical-address-p addr)
       (canonical-address-p (+ -1 (len *copyData*) addr))
       (program-at (create-canonical-address-list (len *copyData*) addr)
                   *copyData* x86)))

(defthm preconditions-fwd-chain-to-its-body
  (implies (preconditions n addr x86)
           (and (x86p x86)
                (xr :programmer-level-mode 0 x86)
                (equal (xr :ms 0 x86) nil)
                (equal (xr :fault 0 x86) nil)
                ;; We are poised to run the copyData sub-routine.
                (equal (xr :rip 0 x86) addr)
                (unsigned-byte-p 31 n)
                (equal (xr :rgf *rdx* x86) n)
                ;; All the stack addresses are canonical.
                (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
                (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
                ;; All the destination addresses are canonical.
                (canonical-address-p (xr :rgf *rsi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rsi* x86)))
                ;; All the source addresses are canonical.
                (canonical-address-p (xr :rgf *rdi* x86))
                (canonical-address-p (+ (ash n 2) (xr :rgf *rdi* x86)))
                ;; Memory locations of interest are disjoint.
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Destination addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
                (disjoint-p
                 ;; Program addresses
                 (create-canonical-address-list (len *copyData*) addr)
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Destination Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86))
                 ;; Stack
                 (create-canonical-address-list 16 (+ -8 (xr :rgf *rsp* x86))))
                (disjoint-p
                 ;; Source Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rdi* x86))
                 ;; Destination Addresses
                 (create-canonical-address-list (ash n 2) (xr :rgf *rsi* x86)))
                ;; Program is located at addr.
                ;; All program addresses are canonical.
                (canonical-address-p addr)
                (canonical-address-p (+ -1 (len *copyData*) addr))
                (program-at (create-canonical-address-list (len *copyData*) addr)
                            *copyData* x86)))
  :rule-classes :forward-chaining)

(defthm canonical-address-p-limits-thm-3
  ;; [Shilpi]: Move to main books?
  (implies (and (canonical-address-p (+ i x))
                (canonical-address-p (+ (- j) x))
                (integerp x)
                (natp j)
                (natp i))
           (canonical-address-p x))
  :hints (("Goal" :in-theory (e/d* (canonical-address-p signed-byte-p) ()))))

(defthm effects-copyData-pre
  (implies (preconditions n addr x86)
           (equal (x86-run (pre-clk n) x86)
                  (if (< 0 n)
                      (XW
                       :RGF *RAX*
                       (ASH (XR :RGF *RDX* X86) 2)
                       (XW
                        :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
                        (XW
                         :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
                         (XW
                          :RIP 0 (+ 16 (XR :RIP 0 X86))
                          (MV-NTH
                           1
                           (WB
                            (CREATE-ADDR-BYTES-ALIST
                             (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                             (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                            (WRITE-USER-RFLAGS
                             (LOGIOR
                              (LOGHEAD 1
                                       (BOOL->BIT (LOGBITP 31 (XR :RGF *RDX* X86))))
                              (LOGHEAD
                               32
                               (ASH
                                (PF-SPEC64
                                 (LOGHEAD 64
                                          (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                               2)))
                                2))
                              (LOGAND
                               4294967290
                               (LOGIOR
                                (LOGHEAD
                                 32
                                 (ASH
                                  (ZF-SPEC
                                   (LOGHEAD 64
                                            (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                                 2)))
                                  6))
                                (LOGAND
                                 4294967230
                                 (LOGIOR
                                  (LOGHEAD
                                   32
                                   (ASH
                                    (SF-SPEC64
                                     (LOGHEAD 64
                                              (ASH (LOGHEAD 64 (LOGEXT 32 (XR :RGF *RDX* X86)))
                                                   2)))
                                    7))
                                  (LOGAND
                                   4294967166
                                   (BITOPS::LOGSQUASH
                                    1
                                    (XR
                                     :RFLAGS 0
                                     (WRITE-USER-RFLAGS
                                      (LOGIOR
                                       (LOGHEAD 32
                                                (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                                       (LOGAND
                                        4294967226
                                        (LOGIOR (LOGAND 4294965118
                                                        (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                                (LOGHEAD 32
                                                         (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                                              7)))))
                                      16 X86)))))))))
                             2064
                             (WRITE-USER-RFLAGS
                              (LOGIOR
                               (LOGHEAD 32
                                        (ASH (PF-SPEC32 (XR :RGF *RDX* X86)) 2))
                               (LOGAND 4294967226
                                       (LOGIOR (LOGAND 4294965118
                                                       (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86)))
                                               (LOGHEAD 32
                                                        (ASH (SF-SPEC32 (XR :RGF *RDX* X86))
                                                             7)))))
                              16 X86))))))))
                    (XW
                     :RGF *RSP* (+ -8 (XR :RGF *RSP* X86))
                     (XW
                      :RGF *RBP* (+ -8 (XR :RGF *RSP* X86))
                      (XW
                       :RIP 0 (+ 34 (XR :RIP 0 X86))
                       (MV-NTH
                        1
                        (WB
                         (CREATE-ADDR-BYTES-ALIST
                          (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -8 (XR :RGF *RSP* X86)))
                          (BYTE-IFY 8 (LOGHEAD 64 (XR :RGF *RBP* X86))))
                         (WRITE-USER-RFLAGS
                          (LOGIOR
                           4
                           (LOGAND 4294967290
                                   (LOGIOR 64
                                           (LOGAND 4294965054
                                                   (BITOPS::LOGSQUASH 1 (XR :RFLAGS 0 X86))))))
                          16 X86)))))))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules

                                    gpr-and-spec-4
                                    jcc/cmovcc/setcc-spec
                                    sal/shl-spec
                                    sal/shl-spec-64

                                    opcode-execute
                                    !rgfi-size
                                    x86-operand-to-reg/mem
                                    wr64
                                    wr32
                                    rr32
                                    rr64
                                    rm32
                                    rm64
                                    wm32
                                    wm64
                                    rr32
                                    x86-operand-from-modr/m-and-sib-bytes
                                    rim-size
                                    rim32
                                    n32-to-i32
                                    n64-to-i64
                                    rim08
                                    two-byte-opcode-decode-and-execute
                                    x86-effective-addr
                                    subset-p)

                                   (wb-remove-duplicate-writes
                                    create-canonical-address-list
                                    force (force))))))

(defthm effects-copyData-pre-programmer-level-mode-projection
  (implies (preconditions n addr x86)
           (equal (xr :programmer-level-mode 0 (x86-run (pre-clk n) x86))
                  (xr :programmer-level-mode 0 x86)))
  :hints (("Goal"
           :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rsi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rdi-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rdi* (x86-run (pre-clk n) x86))
                  (xr :rgf *rdi* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rsp-projection
  (implies (preconditions n addr x86)
           (equal (xr :rgf *rsp* (x86-run (pre-clk n) x86))
                  (+ -8 (xr :rgf *rsp* x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rax-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rgf *rax* (x86-run (pre-clk n) x86))
                  (ash n 2)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-program-at-projection
  (implies (and (preconditions n addr x86)
                (equal prog-len (len *copydata*)))
           (equal (program-at (create-canonical-address-list prog-len addr)
                              *copyData* (x86-run (pre-clk n) x86))
                  (program-at (create-canonical-address-list prog-len addr)
                              *copyData* x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-fault-projection
  (implies (preconditions n addr x86)
           (equal (xr :fault 0 (x86-run (pre-clk n) x86))
                  (xr :fault 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-ms-projection
  (implies (preconditions n addr x86)
           (equal (xr :ms 0 (x86-run (pre-clk n) x86))
                  (xr :ms 0 x86)))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-rip-projection
  (implies (and (preconditions n addr x86)
                (not (zp n)))
           (equal (xr :rip 0 (x86-run (pre-clk n) x86))
                  (+ 16 (xr :rip 0 x86))))
  :hints (("Goal" :use ((:instance effects-copydata-pre))
           :in-theory (e/d* ()
                            ((pre-clk) pre-clk force (force))))))

(defthm effects-copyData-pre-x86p-projection
  (implies (preconditions n addr x86)
           (x86p (x86-run (pre-clk n) x86)))
  :hints (("Goal" :in-theory (e/d* () ((pre-clk) pre-clk force (force))))))

(encapsulate
 ()

 (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))

 (defthm mod-thm-2
   (implies (natp n)
            (equal (mod (ash n 2) 4) 0))
   :hints (("Goal" :in-theory (e/d* (ash) ())))))

(defthm preconditions-implies-loop-preconditions-after-pre-clk
  (implies (and (preconditions n addr x86)
                (not (zp n))
                (equal m (ash n 2)))
           (loop-preconditions
            0 m addr
            (xr :rgf *rdi* x86) ;; src-addr
            (xr :rgf *rsi* x86) ;; dst-addr
            (x86-run (pre-clk n) x86)))
  :hints (("Goal" :hands-off (x86-run)
           :use ((:instance preconditions-fwd-chain-to-its-body))
           :in-theory (e/d* (unsigned-byte-p)
                            (pre-clk
                             (pre-clk) preconditions
                             preconditions-fwd-chain-to-its-body)))))

;; (i-am-here)

;; (defthmd x86-run-plus-for-clk
;;   (equal (x86-run (binary-clk+ (pre-clk n) (loop-clk (ash n 2))) x86)
;;          (x86-run (loop-clk (ash n 2)) (x86-run (pre-clk n) x86)))
;;   :hints (("Goal" :in-theory (e/d* (binary-clk+)
;;                                    (x86-run-plus
;;                                     (loop-clk)
;;                                     loop-clk
;;                                     pre-clk
;;                                     (pre-clk)))
;;            :use ((:instance x86-run-plus
;;                             (n2 (loop-clk (ash n 2)))
;;                             (n1 (pre-clk n)))))))

;; (defthm effects-copyData-n->-0 ;; (1)
;;   (implies (and (preconditions n addr x86)
;;                 (not (zp n))
;;                 (equal m (ash n 2)))
;;            (equal (destination-bytes m (+ m (xr :rgf *rdi* x86)) (x86-run (clk n) x86))
;;                   (source-bytes m (+ m (xr :rgf *rsi* x86)) x86)))
;;   :hints (("Goal"
;;            :use ((:instance preconditions-implies-loop-preconditions-after-pre-clk)
;;                  (:instance loop-copies-m-bytes-from-source-to-destination
;;                             (src-addr (xr :rgf *rdi* x86))
;;                             (dst-addr (xr :rgf *rsi* x86))))
;;            :in-theory (e/d* (x86-run-plus-for-clk)
;;                             (wb-remove-duplicate-writes
;;                              preconditions-implies-loop-preconditions-after-pre-clk
;;                              loop-copies-m-bytes-from-source-to-destination
;;                              effects-copydata-pre
;;                              preconditions
;;                              destination-bytes
;;                              source-bytes
;;                              (loop-clk)
;;                              loop-clk
;;                              pre-clk
;;                              (pre-clk)
;;                              create-canonical-address-list
;;                              force (force))))))


;; (2) Prove a theorem similar to effects-copyData-n->-0, but it should be in terms of program-clk.

;; (3) Prove the top-level theorem that removes (not (zp n)) from the hyps. of (2).
