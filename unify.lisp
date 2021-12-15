; unify.l carries out simple resolution. It is pretty much
; the code from AIP. 

(load "objects.lisp")
(load "sets.lisp")

; A unification is a data-type. POSLIT is the positive literal
; unified; NEGLIT, the negative literal; BDGS, the bindings

(defstruct unification 
  POSLIT 
  NEGLIT 
  BDGS)

(declare (special *COMMON-VARS*)) ; List of shared variable names

; Utilities for dealing with the *VAR* notation

(defun is-pcvar (X) (and (listp X) (eq (car X) '*VAR*)))

(defmacro get-var (X) `(cadr ,X))

; (resolve CL1 CL2) returns a list of all possible resolutions of
; skolem-clauses CL1 and CL2

(defun resolve (CL1 CL2)
   (setq CL2 (vars-rename CL2 (var-conflict CL1 CL2)))
   (nconc (resolve1 CL1 CL2) (resolve1 CL2 CL1)))

; var-conflict returns a list of all the variables shared by CL1 and
; CL2, together with new names for them.

(defun var-conflict (CL1 CL2)
  (let ((*COMMON-VARS* nil))
    (extract-vars CL1 (flambda (VAR) (putprop VAR t 'VAR-CONFLICT)))
    (extract-vars CL2 
       (flambda (VAR) (cond ((get VAR 'VAR-CONFLICT)
                             (remprop VAR 'VAR-CONFLICT)
                             (push `(,VAR (*VAR* ,(gensym))) 
                                   *COMMON-VARS*)))))
    (extract-vars CL1 (flambda (VAR) (remprop VAR 'VAR-CONFLICT)))
    *COMMON-VARS*))
    
   
; extract-vars applies FUN to all the variables in FORM

(defun extract-vars (FORM FUN)
    (cond ((atom FORM))
          ((is-pcvar FORM)
           (funcall FUN (get-var FORM)))
          (t
           (extract-vars (car FORM) FUN)
           (extract-vars (cdr FORM) FUN))))

; vars-rename eliminates shared variables from FORM. RENAME-VARS
; is an alist of shared variables with the new variable.

(defun vars-rename (FORM RENAME-VARS)
    (cond ((null RENAME-VARS) FORM)
          (t
           (vars-rename1 FORM RENAME-VARS))))

; vars-rename1 does the real work of vars-rename

(defun vars-rename1 (FORM RENAME-VARS)
   (cond ((atom FORM) FORM)
         ((is-pcvar FORM)
          (or (associated (get-var FORM) RENAME-VARS)
              FORM))
         (t
          (cons (vars-rename1 (car FORM) RENAME-VARS)
                (vars-rename1 (cdr FORM) RENAME-VARS)))))
          

; resolve1 finds all resolvants of CL1 and CL2 involving a
; positive literal from CL1 and a negative from CL2.

(fundecl resolve1 (lst skolem-clause) (skolem-clause CL1 CL2)
    (loop for UNIF in (unifiers (POSLITS CL1) (NEGLITS CL2))
      do save (find-resolvant CL1 CL2 UNIF)))

; (unifiers LITS1 LITS2) returns all the unifiers which will
; unify a literal in LITS1 with one in LITS2

(defun unifiers (LITS1 LITS2)
     (loop for LIT1 in LITS1
        do splice 
          (loop for LIT2 in LITS2
             do splice (unify-lit LIT1 LIT2))))

; (unify-lit LIT1 LIT2) returns the unification of literals LIT1
; and LIT2, if any

(defun unify-lit (LIT1 LIT2)
   (let ((SUBS (unify LIT1 LIT2)))
      (cond (SUBS
             (list (make-unification :POSLIT LIT1 :NEGLIT LIT2
                              :BDGS (collapse-bindings (car SUBS))))))))

; (collapse-bindings SUBS) collapses multiple levels of bindings
; in SUBS (See AIP, ex. 13.4). collapse-binding and deep-varsubst
; are subroutines.

(defun collapse-bindings (SUBS)
   (loop for BDG in SUBS
     do (collapse-binding BDG SUBS)))


(defun collapse-binding (BDG SUBS)
   (let ((NEW-VAL (deep-varsubst (cadr BDG) SUBS)))
      (setf (cadr BDG) NEW-VAL)
      NEW-VAL))

(defun deep-varsubst (FORM SUBS)
   (cond ((atom FORM) FORM)
         ((is-pcvar FORM)
          (let ((BDG (assoc (get-var FORM) SUBS)))
            (cond (BDG (collapse-binding BDG SUBS))
                  (t FORM))))
         (t
          (cons (deep-varsubst (car FORM) SUBS)
                (deep-varsubst (cdr FORM) SUBS))))) 
   
; find-resolvant computes the resolvant of CL1 with CL2 under
; unification UNIF

(fundecl find-resolvant skolem-clause (skolem-clause CL1 CL2 
                                       unification UNIF)
  (make-instance skcl 'skolem-clause) 
      (setf (POSLITS skcl) (varsubst (append (POSLITS CL2)
                        (remq (POSLIT-unification UNIF) (POSLITS CL1)))
                (BDGS-unification UNIF)))
      (setf (NEGLITS skcl) (varsubst (append (NEGLITS CL1)
                        (remq (NEGLIT-unification UNIF) (NEGLITS CL2)))
                (BDGS-unification UNIF))))

; (varsubst FORM BDGS) modifies FORM with the bindings in BDGS

(defun varsubst (FORM BDGS)
    (cond ((atom FORM) FORM)
          ((is-pcvar FORM)
           (or (sym-lookup FORM BDGS) FORM))
          (t
           (cons (varsubst (car FORM) BDGS) (varsubst (cdr FORM) BDGS)))))
   
      
; This is exactly the unification code from AIP.

(defun unify (PAT1 PAT2) 
   (unify1 PAT1 PAT2 nil))

(defun unify1 (PAT1 PAT2 SUB)
  (cond ((is-pcvar PAT1)
         (var-unify PAT1 PAT2 SUB))
        ((is-pcvar PAT2)
         (var-unify PAT2 PAT1 SUB))
        ((atom PAT1)
         (cond ((eq PAT1 PAT2)
                (list SUB))))
        ((atom PAT2) nil)
        (t
         (let ((CAR-SUBSTS (unify1 (car PAT1) (car PAT2) SUB)))
            (cond (CAR-SUBSTS
                   (unify1 (cdr PAT1) (cdr PAT2) (car CAR-SUBSTS))))))))

(defun var-unify (V PAT SUB)
   (let ((VAR (get-var V)) (BDG (sym-lookup V SUB)))
     (cond (BDG 
            (unify1 BDG PAT SUB))
           ((equal V PAT) 
            (list SUB))
           ((not (occurs-in V PAT SUB))
            (list (cons (list VAR PAT) SUB))))))

(defun occurs-in  (V P SUB)
   (cond ((atom P) nil)
         ((is-pcvar P)
          (or (equal V P)
              (let ((B (sym-lookup P SUB)))
                 (and B (occurs-in V B SUB)))))
         (t
          (some (flambda (Y) (occurs-in V Y SUB)) P))))


(defun sym-lookup (V SUB)
   (cadr (assoc (get-var V) SUB)))
