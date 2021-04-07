; This is file basic-macs.l

(defmacro putprop (var val prop); sets the property "prop" of plist variable "var" to value "val"
  `(setf (get ,var ,prop) ,val))
  ;get grabs a certain property of a plist variable
  ;setf sets that property to the new value

; push and pop from the head of a list
(defmacro push (X L) `(setq ,L (cons ,X ,L)))


(defmacro pop (L) `(prog1 (car ,L) (setq ,L (cdr ,L))))


; ; load a collection of unquoted files
; (defun dskin fexpr (L)
;    (mapc 'dskin1 L))
;
;
;
; (defun dskin1 (F)
;    (cond ((not (get F 'LOADED))
;           (load F)
;           (msg F " loaded" N)
;           (putprop F t 'LOADED))))


(defmacro flambda (&rest L)
   `(function (lambda ,@L)))


; ; Return the tail of !!L starting at the first element !!X for which
; ; (!!FUN !!X) is non-null
;
; (defun some (!!FUN !!L)
;    (prog (!!X)
;      loop (cond ((null !!L) (return nil)))
;           (setq !!X (car !!L))
;           (cond ((funcall !!FUN !!X) (return !!L)))
;           (setq !!L (cdr !!L))
;           (go loop)))
;
;
; ; Check that every element of !!L returns non-null under !!FUN
;
; (defun every (!!FUN !!L)
;    (prog (!!X)
;      loop (cond ((null !!L) (return t)))
;           (setq !!X (car !!L))
;           (cond ((not (funcall !!FUN !!X)) (return nil)))
;           (setq !!L (cdr !!L))
;           (go loop)))


; Steps through the lists in !!LS in lockstep, checking that !!FUN
; always returns non-null. Like mapping functions with many arguments.

(defun every-list (!!FUN &rest !!LS)
   (prog (); executes a sequence of code. "go" and "return" can be used
      loop; <- this is NOT a loop function. look at "go" at the bottom
      (cond ((memq nil !!LS) (return t)));when list is empty, return t
      (cond ((not (apply !!FUN (mapcar 'car !!LS))) (return nil))); grabs first element of every list, pass them in as arguemnt to function !!FUN. If it returns  null, return null.
      (setq !!LS (mapcar 'cdr !!LS));removes first element of every list. Proceed
      (go loop)
    )
)

; (defun list-if-there (X) (and X (list X)))
;
;
; ; return !!L with no duplicates elements. !!FUN is the equality
; ; comparator. This function is destructive.
;
; (defun remove-duples (!!FUN !!L)
;    (prog (!!L1 !!L2)
;      (setq !!L1 !!L)
;      loop1 (setq !!L2 !!L1)
;            (cond ((null (cdr !!L2)) (return !!L)))
;      loop2 (cond ((funcall !!FUN (car !!L1) (cadr !!L2))
;                   (rplacd !!L2 (cddr !!L2))))
;            (setq !!L2 (cdr !!L2))
;            (cond (!!L2 (go loop2))
;                  (t
;                   (setq !!L1 (cdr !!L1))
;                   (go loop1)))))



(defmacro associate (X L)
  `(cadr (assoc ,X ,L)))


(defmacro top-copy (X) `(append ,X nil))


(defun inner-member (X L)
   (cond ((equal X L))
         ((atom L) nil)
         ((inner-member X (car L)))
         ((inner-member X (cdr L)))))

; An and which evaluates all its arguments.
(defmacro full-and (&rest L)
   `(let ((!!V t))
      ,@(mapcar (flambda (X) `(setq !!V (and ,X !!V))) L)))
