
(defmacro fundecl (FUNNAME FUNTYPE VARLIST &rest BODY)
    (putprop FUNNAME FUNTYPE 'FUNTYPE); stores function type of function
    (let* ((PARSED (parse-decl VARLIST))
           (*DECL-TYPES* (car PARSED)) ;"car parsed"=type-pairs, ex: ((arg1 type1) (arg2 type1)...).
           (ARGLIST (cadr PARSED))) ;"cadr parsed"=arglist, ex: (arg1 arg2 arg3...)
      `(defun ,FUNNAME ,(reverse ARGLIST) ,@(colon-expand BODY)))) ; turned every field access to

(defun parse-decl (VARLIST)
   (let (TYPE-PAIRS ARGLIST TYPE NEXT-SYM)
      (loop (while VARLIST); while varlist is not empty
            (do (setq NEXT-SYM (car VARLIST));set next-sym has first varlist
                (cond ((is-type NEXT-SYM); if next-sym is a type, set type to next-sym
                       (setq TYPE NEXT-SYM));
                      ((atom NEXT-SYM); if next-sym is an atom, push next-sym into arglist, and push the pair (next-sym, type) into type-pairs
                       (push NEXT-SYM ARGLIST)
                       (push (list NEXT-SYM TYPE) TYPE-PAIRS))
                      (t; else, its a list
                       (push (list (car NEXT-SYM) (macroexpand (cadr NEXT-SYM))) ARGLIST); pushes a list into arglist
                       (push (list (car NEXT-SYM) TYPE) TYPE-PAIRS))));pushed a list
            (next VARLIST (cdr VARLIST)));remove first element
      (list TYPE-PAIRS ARGLIST)));returns type-paris and arglist

(defun is-type (TYPE)
   (and (atom TYPE) (get TYPE 'RECORD-TYPE))); if TYPE is an atom (Symbols, numbers and strings), and "RECORD-TYPE" not null
