; find the union of the lists of atoms in !LLS

(defun atom-union-over (!LLS !FUN)
   (let ((!UNION
           (loop for !L in !LLS
             do (splice (loop for !X in (funcall !FUN !L)
                       do (when (not (get !X 'atom-union-over)))
                       (save (progn (putprop !X t 'atom-union-over)
                                    !X)))))))
     (loop for !X in !UNION
        do (remprop !X 'atom-union-over))
     !UNION))

; determine whether !L is a subset of !M (both are lists of atoms).

(defun atom-subset (!L !M)
   (let (VERIFIED)
     (loop for !X in !M do (putprop !X t 'atom-subset))
     (setq VERIFIED
        (every (flambda (!X) (get !X 'atom-subset)) !L))
     (loop for !X in !M do (remprop !X  'atom-subset))
     VERIFIED))

(defun is-subset (!L !M &optional !FUN)
   (cond ((null !FUN)
          (every (flambda (!Z) (memq !Z !M)) !L))
         ((eq !FUN 'equal)
          (every (flambda (!Z) (member !Z !M)) !L))
         (t
          (every (flambda (!Z)
                   (some (flambda (!QQQ) (funcall !FUN !Z !QQQ))
                         !M)
                   !L)))))

; find the set difference between !L and !M under equality comparator
; !FUN
(defun set-diff (!L !M &optional !FUN)
   (cond ((null !FUN)
          (loop for !Z in !L 
            do (when (not (memq !Z !M))) 
            (save !Z)))
         ((eq !FUN 'equal)
          (loop for !Z in !L 
            do (when (not (member !Z !M))) 
            (save !Z)))
         (t
          (loop for !Z in !L 
            do (when (not (some (flambda (!Q) (funcall !FUN !Z !Q)) !M)))
            (save !Z)))))
