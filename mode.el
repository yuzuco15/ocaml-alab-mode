;; (progn
;;   ;(call-process "pwd" nil t)
  
;;   (print (point))
;; )

(defun printcat ()
  (interactive)
  (progn (print 'The\ cat\ in)
       (print "the hat")
       (print " came back")))
;; exit(*{}*)0
