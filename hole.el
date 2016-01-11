;; set the path to expander*
(defvar path "/Users/YukiIshii/lab/expander/expander")

;; hole for expression
;; let f: 'a -> 'a = (exit 0)
(defvar hole "(exit(*{}*)0)")
;; prefix and suffix of hole for regular expression
;; (exit(\*{<p><q>}\*)n)<r>
(defvar hole-p "(exit(\\*{")
(defvar hole-q "}\\*)")
(defvar hole-r "[0-9]+)")

;; hole for pattern
;; let f: (_) = fun x -> x;;
(defvar pattern-hole "(_(*{}0*))")
;; prefix and suffix of pattern-hole for regular expression
;; (_(\*{<p><q>}n\*))<r>
(defvar pattern-hole-p "(_(\\*{")
(defvar pattern-hole-q "}[0-9]+")
(defvar pattern-hole-r "\\*)")

;; minor mode
;; `M-x hole-mode` to use this mode.
(define-minor-mode hole-mode nil nil 
  :lighter "+Hole" 
  :keymap '( 
	    ("\C-cg" . agda2-go) 
	    ("\C-cr" . refine-goal) 
	    ("\C-c," . refine-goal-with-argument) 
	    ("\C-cm" . match-variable) 
	    ("\C-cc" . agda2-forget-this-goal) 
	    ("\C-cf" . agda2-forget-all-goals) 
	    ("\C-ci" . refine-if-statement) 
	    ("\C-cs" . show-goal) 
	    ("\C-ch" . put-hole)
	    ("\C-cn" . agda2-next-goal)
	    ("\C-cb" . agda2-previous-goal)
	    ("\C-ce" . expand-syntax)
	    ) 
  :group 'tuareg)

;; infomation window

;; The maximum height of the information window.
;; A multiple of the frame height.
(defvar information-window-max-height 0.35)

(defvar expander-buffer nil "expander buffer")
(defvar info-buffer nil "info buffer")

(defun expander-buffer ()
  "Creates the expander buffer, if it does not already exist.
The buffer is returned."
  (if (buffer-live-p expander-buffer)
    expander-buffer
    (let ((buf (generate-new-buffer "*expander output*")))
      (setq expander-buffer buf)
      buf)))

(defun info-buffer ()
  "Creates the info buffer, if it does not already exist.
The buffer is returned."
  (if (buffer-live-p info-buffer)
    info-buffer
    (let ((buf (generate-new-buffer "*expander information*")))
      (setq info-buffer buf)
      buf)))

(defun info-action (text)
  "Insert TEXT into the info buffer and display it."
  (interactive)
  (with-current-buffer (info-buffer)
    (erase-buffer)
    (save-excursion
      (insert text))
    (save-selected-window
      (let ((split-width-threshold nil)
	    (buf (current-buffer)))
	(pop-to-buffer buf nil 'norecord)
	(fit-window-to-buffer nil
          (truncate (* (frame-height) information-window-max-height)))
	(goto-char (point-min))))))

(defun expander-to-info ()
  "Copies the context of expander buffer to info buffer."
  (with-current-buffer (expander-buffer)
    (info-action (buffer-string))))

(defun call-expander (filename num command &optional arg)
  "Saves the current buffer, calls expander, and
stores the result in (expander-buffer) including the error case."
  (progn
    (save-buffer)
    (with-current-buffer (expander-buffer)
      (erase-buffer)
      (if arg
	(call-process path nil (expander-buffer) nil "-w" "-A"
		      filename num command arg)
	(call-process path nil (expander-buffer) nil "-w" "-A"
		      filename num command)))))

(defun result-error-p ()
  "Returns t if (expander-buffer) contains an error."
  (with-current-buffer (expander-buffer)
    (let ((answer (buffer-string)))
      (or (string-match "Error*" answer)
	  (string-match "Warning*" answer)))))

;; goal position and number
(defun agda2-goal-at (pos)
  "Return (goal overlay, goal number) at POS, or nil."
  (let ((os (and pos (overlays-at pos))) o g)
    (while (and os (not(setq g (overlay-get (setq o (pop os)) 'agda2-gn)))))
    (if g (list o g))))

(defun agda2-goal-overlay (g)
  "Returns the overlay of goal number G, if any."
  (car
   (remove nil
           (mapcar (lambda (o) (if (equal (overlay-get o 'agda2-gn) g) o))
                   (overlays-in (point-min) (point-max))))))

(defun agda2-range-of-goal (g)
  "The range of goal G."
  (let ((o (agda2-goal-overlay g)))
    (if o (list (overlay-start o) (overlay-end o)))))

;; from annotation.el
(defmacro annotation-preserve-mod-p-and-undo (&rest code)
  "Run CODE preserving both the undo data and the modification bit.
Modification hooks are also disabled."
  (let ((modp (make-symbol "modp")))
  `(let ((,modp (buffer-modified-p))
         ;; Don't check if the file is being modified by some other process.
         (buffer-file-name nil)
         ;; Don't record those changes on the undo-log.
         (buffer-undo-list t)
         ;; Don't run modification hooks.
         (inhibit-modification-hooks t))
     (unwind-protect
         (progn ,@code)
       (restore-buffer-modified-p ,modp)))))

;; Annotation for a goal
;; exit(*{ ... }*)3
;; ----------------  overlay: agda2-gn num, face highlight, after-string num,
;;                            modification-hooks (agda2-protect-goal-markers)
;; -------           text-props: category agda2-delim1
;;             ----  text-props: category agda2-delim2

;; Char categories for the goal
(defvar agda2-open-brace "{")
(defvar agda2-close-brace " }")
(setplist 'agda2-delim1 `(display ,agda2-open-brace rear-nonsticky t
				  agda2-delim1 t))
(setplist 'agda2-delim2 `(display ,agda2-close-brace rear-nonsticky t
				  agda2-delim2 t))

(defun agda2-make-goal (p q r)
  "Make a goal at (exit(\*{<p><q>}\*)n)<r>."
  (annotation-preserve-mod-p-and-undo
   (let ((n (buffer-substring (+ q 3) (- r 1)))
	 (o (make-overlay (- p 8) r nil t nil)))
      ;;(print n)
      (add-text-properties (- p 8) p '(category agda2-delim1))
      (add-text-properties q r '(category agda2-delim2))
      (overlay-put o 'agda2-gn           n)
      (overlay-put o 'modification-hooks '(agda2-protect-goal-markers))
      (overlay-put o 'face               'highlight)
      (overlay-put o 'after-string       (propertize (format "%s" n) 'face 'highlight))
      o )))

;; (_(\\*{<p>...<q>}[0-9]+\\*))<r>
(defun agda2-make-goal-pattern (p q r)
  "Make a goal at (_(\*{<p>...<q>}n\*))<r>."
  (annotation-preserve-mod-p-and-undo
   (let ((n (buffer-substring (+ q 1) (- r 3)))
	 (o (make-overlay (- p 5) r nil t nil)))
      ;;(print n)
      (add-text-properties (- p 5) p '(category agda2-delim1))
      (add-text-properties q r '(category agda2-delim2))
      (overlay-put o 'agda2-gn           n)
      (overlay-put o 'modification-hooks '(agda2-protect-goal-markers))
      (overlay-put o 'face               'highlight)
      (overlay-put o 'after-string       (propertize (format "%s" n) 'face 'highlight))
      o )))

(defun agda2-protect-goal-markers (ol action beg end &optional length)
  "Ensures that the goal markers cannot be tampered with.
Except if `inhibit-read-only' is non-nil or /all/ of the goal is
modified."
  (if action
      ;; This is the after-change hook.
      nil
    ;; This is the before-change hook.
    (cond
     ((and (<= beg (overlay-start ol)) (>= end (overlay-end ol)))
      ;; The user is trying to remove the whole goal:
      ;; manually evaporate the overlay and add an undo-log entry so
      ;; it gets re-added if needed.
      (when (listp buffer-undo-list)
        (push (list 'apply 0 (overlay-start ol) (overlay-end ol)
                    'move-overlay ol (overlay-start ol) (overlay-end ol))
              buffer-undo-list))
      (delete-overlay ol))
     ((or (< beg (+ (overlay-start ol) 2))
          (> end (- (overlay-end ol) 2)))
      (unless inhibit-read-only
        (signal 'text-read-only nil))))))

(defmacro agda2-let (varbind funcbind &rest body)
  "Expands to (let* VARBIND (cl-labels FUNCBIND BODY...)).
Or possibly (let* VARBIND (labels FUNCBIND BODY...))."
  ;;`(let* ,varbind (cl-labels ,funcbind ,@body))
  `(let* ,varbind (,(if (fboundp 'cl-labels) 'cl-labels 'labels) ,funcbind ,@body))
  )
;;(put 'agda2-let 'lisp-indent-function 2)

(defun agda2-next-goal ()     "Go to the next goal, if any."     (interactive)
  (agda2-mv-goal 'next-single-property-change     'agda2-delim1 8 (point-min)))
(defun agda2-previous-goal () "Go to the previous goal, if any." (interactive)
  (agda2-mv-goal 'previous-single-property-change 'agda2-delim2 0 (point-max)))
(defun agda2-mv-goal (change delim adjust wrapped)
  (agda2-let ()
      ((go (p) (while (and (setq p (funcall change p 'category))
                           (not (eq (get-text-property p 'category) delim))))
           (if p (goto-char (+ adjust p)))))
    (or (go (point)) (go wrapped) (message "No goals in the buffer"))))

;; for gensym
(defvar hole-number 0)

(defun gensym-hole-number ()
  (setq hole-number (+ hole-number 1))
  )

(defun insert-hole-number (start)
  (goto-char start)
  (insert (number-to-string hole-number))
  )

(defun agda2-search-goal ()
  (if (re-search-forward "(exit(\\*{" nil t 1)
    (let ((p (point))) ;; (exit(\\*{<p>...
      (if (re-search-forward "}\\*)" nil t 1)
	  (progn
	    (let ((q (- (point) 3))) ;; <q>}\\*)
	      ;; remove hole number if the hole has
	      (goto-char q)
	      (cond 
		    ((re-search-forward "}\\*)[0-9]+" nil t 1)
		     ;; need to delete hole number
		     (progn
		       (let ((end (point))) ;; }\\*)[0-9]+<end>)
			 (re-search-backward ")[0-9]+" nil t 1)
			 (let ((start (+ 1 (point)))) ;; }\\*)<start>[0-9]+<end>)
			   (delete-region start end) ;; delete hole number
			   (insert-hole-number start)
			   (goto-char start)
			   (if (re-search-forward "[0-9]+)") ;; [0-9]+)<r>
			       (let ((r (point))) ;; (exit(\\*{<p><q>}\\*)n)<r>
				 (agda2-make-goal p q r)
				 ))))
		       )))
	      ))))))

;; (_(*{<p>...<q>}0*))<r>
;; (defvar pattern-hole-p "(_(\\*{")
;; (defvar pattern-hole-q "}[0-9]+")
;; (defvar pattern-hole-r "\\*)")
(defun agda2-search-goal-pattern ()
  (if (re-search-forward pattern-hole-p nil t 1)
      (let ((p (point))) ;; (_(\\*{<p>...
	(if (re-search-forward "}[0-9]+\\*))" nil t 1) ;; (cons pattern-hole-q pattern-hole-r)
	    (if (re-search-backward "}[0-9]+" nil t 1)
		(let* ((q (point)) ;; <q>}[0-9]+\\*)), pattern-hole-q
		       (start (+ q 1))) ;; <q>}<start>[0-9]+\\*)
		  (if (re-search-forward "[0-9]+\\*") ;;<q>}<start>[0-9]+\\*<temp>))
		      (let ((end (- (point) 1))) ;; <q>}<start>[0-9]+<end>\\*))
			(delete-region start end) ;; delete hole-number
			(insert-hole-number start)
			(goto-char start)
			(if (re-search-forward "[0-9]\\*))" nil t 1) ;; <start>[0-9]+\\*))<r>
			    (let ((r (point))) ;; (_(\\*{<p>...<q>}[0-9]+\\*))<r>
			      (agda2-make-goal-pattern p q r)
			      ))))
		  ))))))

(defun agda2-go ()
  (interactive)
  (save-excursion
    (agda2-forget-all-goals)
    (goto-char (point-min))
    (setq hole-number 0)
    (while (agda2-search-goal)
      (gensym-hole-number)
      ;;(print hole_number)
	   ; no body
      )))

(defun agda2-go-pattern ()
  (interactive)
  (save-excursion
    ;;(agda2-forget-all-goals-pattern)
    (goto-char (point-min))
    (setq hole-number 0)
    (while (agda2-search-goal-pattern)
      (gensym-hole-number)
      ;;(print hole_number)
	   ; no body
      )
    ))

(defun get-expression (start end) ;; <start>(exit(*{}*)n)<end>
  (goto-char end)
  (if (re-search-backward "}\\*)" nil t 1)
      (let* ((expend (point)) ;; <start>(exit(*{...<expend>}*)n)<end>
	     (expression (buffer-substring (+ start 8) expend)))
	;;(message expression)
	expression)))


(defun put-hole ()
  (interactive)
  (let ((start (point)))
    (insert hole)
    (agda2-go)
    (goto-char (+ start 8))
  ))

(defun delete-expression (expression)
       (goto-char (point))
       (let ((end (point)))
	 (if (re-search-backward expression nil t 1)
	     (let ((start (point)))
	       (delete-region start end)))))

(defun refine-goal-with-argument ()
  (interactive)
  (let ((overlay-and-number (agda2-goal-at (point))))
    (if overlay-and-number
      (let* ((num (car (cdr overlay-and-number)))
	     (range (agda2-range-of-goal num))
	     (start (car range)) ;; <start>(exit(*{}*)n)<end>
	     (end (car (cdr range)))
	     (expression (get-expression start end))
	     (filename (buffer-file-name)))
	;; delete this hole and insert the expression that user input
	(agda2-reset) ;; delete this hole
	(insert expression) ;; insert expression
	(call-expander filename num "RefineArg" expression)
	(if (result-error-p)
	  (progn ;; delete `word` and insert hole
	    (delete-expression expression)
	    (put-hole)
	    (expander-to-info) ; show error
	    (message "Cannot Refine"))
	  (progn
	    (expander-to-info) ; clear info buffer
	    (ocp-indent-buffer)
	    (save-buffer)
	    (agda2-go))) ;; reset all the hole numbers
	)
      (message "First move to a goal."))))

 (defun refine-goal ()
  (interactive)
  (let* ((filename (buffer-file-name))
	(overlay-and-number (agda2-goal-at (point))) ;; "Return (goal overlay, goal number) at POS, or nil."
	(num (car (cdr overlay-and-number))))
    (progn
      ;; create buffer for return value from expander
      (generate-new-buffer "expander-buffer")
      ;; save
      (save-buffer)
      (let ((refine-buffer (buffer-name))) ;; current buffer name
;;	(split-window-below)
;;	(set-window-buffer nil "expander-buffer")
	(call-process path nil "expander-buffer" nil "-w" "-A" filename num "Refine")
	(progn
	  (let ((answer (with-current-buffer "expander-buffer"
			  (buffer-string))
			  ))
	    (if (or (string-match "Error:*" answer)  (string-match "Warning*" answer))
		(message "%s" answer)
	      (progn
		(agda2-reset)
		(insert answer)
		(let ((p (point)))
		  (ocp-indent-buffer)
		  (save-buffer)
		  (agda2-go)
		  (goto-char p)
		))
	      )
	    (kill-buffer "expander-buffer")
	    ))
	))))

(defun match-variable ()
  (interactive)
  (let* ((overlay-and-position (agda2-goal-at (point)))
	 (num (car (cdr overlay-and-position)))
	 (range (agda2-range-of-goal num))
	 (start (car range))
	 (end (car (last range)))
	 (expression (get-expression start end))
    	 (filename (buffer-file-name)))
    (progn
       (generate-new-buffer "expander-buffer")
       ;; insert let a = g 3 in {a }0
       (agda2-reset)
       (let ((tempstart (point))
	     (temp-str (concat "let a = " (concat expression " in (exit(*{a}*)0)"))))
	 (insert temp-str)
	 (let ((tempend (point)))
	   (agda2-go) ;; set the hole number
	   (save-buffer)
	   ;; expander.ml always gets type of variable "a" instead of expression
	   (call-process path nil "expander-buffer" nil "-w" "-A" filename num "Match" expression)
	   (progn
	     (let ((answer (with-current-buffer "expander-buffer"
			     (buffer-string))
			   ))
	       (if (or (string-match "Error:*" answer) (string-match "Warning*" answer))
		   (message "%s" answer)
		 (progn
		   (delete-region tempstart tempend)
		   (goto-char tempstart)
		   (insert answer)
		   (let ((p (point)))
		     (ocp-indent-buffer)
		     (save-buffer)
		     (agda2-go)
		     (goto-char p)
		   ))))
	       (kill-buffer "expander-buffer")
	       ))))))

(defun refine-if-statement ()
  (interactive)
  (let* ((filename (buffer-file-name))
	 (overlay-and-position (agda2-goal-at (point)))
	 (num (car (cdr overlay-and-position))))
    (progn
      (generate-new-buffer "expander-buffer")
      (save-buffer)
      (call-process path nil "expander-buffer" nil "-w" "-A" filename num "If")
      (progn
	(let ((answer (with-current-buffer "expander-buffer"
			(buffer-string))))
	  (if (or (string-match "Error:*" answer) (string-match "Warning*" answer))
	      (message "%s" answer)
	    (progn
	      (agda2-reset)
	      (insert answer)
	      (let ((p (point)))
		(ocp-indent-buffer)
		(save-buffer)
		(agda2-go)
		(goto-char p)
	      )))
	  (kill-buffer "expander-buffer")
	  )))))

(defun replace-goal (&rest texts)
  (progn
    (agda2-remove-hole)
    (save-excursion
      (insert (apply #'concat texts))
      (ocp-indent-buffer)
      (save-buffer)
      (agda2-go))
    (agda2-next-goal)))

(defun expand-syntax ()
  (interactive)
  (let ((overlay-and-position (agda2-goal-at (point))))
    (if overlay-and-position 
      (let* ((num (car (cdr overlay-and-position)))
	     (range (agda2-range-of-goal num))
	     (start (car range))
	     (end (car (cdr range)))
	     (expression (get-expression start end)))
	(cond ((string-match-p "^ *if *$" expression)
	       (replace-goal "if " hole " then " hole " else " hole))
	      ((string-match-p "^ *let *$" expression)
	       (replace-goal "let " hole " = " hole " in " hole))
	      ((string-match-p "^ *fun *$" expression)
	       (replace-goal "fun " hole " -> " hole))
	      ((string-match-p "^ *:: *$" expression)
	       (replace-goal hole " :: " hole))
	      ((string-match-p "^ *$" expression)
	       (message "Input keyword to expand.")
	       )
	      (t ; error.
	       (message "Unknown keyword.")
	       )))
      (message "First move to a goal."))))

(defun show-goal ()
  (interactive)
  (let ((filename (buffer-file-name))
	(overlay-and-position (agda2-goal-at (point))))
    (if overlay-and-position
      (let ((num (car (cdr overlay-and-position))))
	(call-expander filename num "ShowGoal")
	(expander-to-info))
      (message "First move to a goal."))))

;; erase hole
;;  (add-text-properties (- p 7) p '(category agda2-delim1))
;;  (add-text-properties q r '(category agda2-delim2))
(defun agda2-remove-hole ()
  (progn
    (agda2-search-hole-backward)
    (goto-char (point))
    ;; remove hole
    (if (re-search-backward "(exit(\\*{" nil t 1)
	(let ((p (point))) ;; <p>(exit(\\*{
	  (if (re-search-forward "}\\*)[0-9]+)" nil t 1)
	      (let ((q (point))) ;; }\\*)n)<q>
	;; 	(if (re-search-forward "[0-9]+" nil t 1)
;; 		    (let ((r (point)))
;; ;;		      (print "delete-region")
		      (delete-region p q)))))))

(defun delete-lays (lays)
  (let (value)
    (dolist (elt lays value)
      (delete-overlay elt)))) ;; e.g. {v }3 with highlight -> {v } without highlight
  
(defun agda2-reset ()
  ;;(interactive)
  (progn
    (goto-char (point))
    ;; (agda2-search-hole)))
    (while (agda2-remove-hole)
      ;; no body
      )))

(defun agda2-search-hole-backward ()
  (if (re-search-backward "(exit(\\*{" nil t 1)
    (let ((p (point))) ;; <p>(exit(\\*{
      (if (re-search-forward "}\\*)" nil t 1)
	(let ((q (point))) ;; }\\*)<q>
	  (if (re-search-forward "[0-9]+)" nil t 1)
	      (let* ((r (point)) ;; [0-9]+)<r>
		     (lays (overlays-in p r)))
		(delete-lays lays) ;; delete hole number and highlight
		;; remove text properties -> (exit(*{ }*)n) appears
		(remove-text-properties p (+ p 8) '(category agda2-delim1))
		(remove-text-properties (- q 3) r '(category agda2-delim2))
		(goto-char (point))
	  	)
	    )
	  )))))

;; clear all the holes in *.ml
(defun agda2-search-hole () ;; (exit(\\*{<p>}\\*)<q>[0-9]+)<r>
  (if (re-search-forward "(exit(\\*{" nil t 1)
    (let ((p (point)))
      (if (re-search-forward "}\\*)" nil t 1)
	(let ((q (point)))
	  (if (re-search-forward "[0-9]+)" nil t 1)
	      (let* ((r (point))
		     (lays (overlays-in p r)))
		(delete-lays lays) ;; delete hole number and highlight
		;; remove text properties -> (exit(*{}*)n) appears
		(remove-text-properties (- p 8) p '(category agda2-delim1))
		(remove-text-properties (- q 3) r '(category agda2-delim2))
		;;(goto-char (point))
	  	)
	    )
	  )))))

;; clear all the pattern-holes in *.ml
(defun agda2-search-hole-pattern ()
  (message "start" ;; hole: (_(*{}0*))
  (if (re-search-forward "(_(\\*{" nil t 1)
      (progn
	(message "found p")
	(let ((p (point))) ;; (_(\\*{<p>
	  (if (re-search-forward "}[0-9]+\\*))" nil t 1)
	      (let ((r (point))) ;; }[0-9]+\\*))<r>
		(message "r")
		(if (re-search-backward "}[0-9]+\\*))" nil t 1)
		    (let* ((q (point)) ;; <q>}[0-9]+\\*))
			   (lays (overlays-in p r)))
		      (message "p, q, r") ;; (_(\\*{<p>...<q>}[0-9]+\\*))<r>
		      (delete-lays lays) ;; delete highlight
		      ;; remove text properties -> (_(*{}n*)) appears
		      (remove-text-properties (- p 5) p '(category agda2-delim1))
		      (remove-text-properties q r '(category agda2-delim2))
		      (goto-char (point))
		      )
		  )
		)))))))

(defun agda2-forget-this-goal ()
  (interactive)
  (goto-char (point))
  (agda2-search-hole-backward)
  (agda2-remove-hole))

(defun agda2-forget-all-goals ()
  (interactive)
  (progn
    (goto-char (point-min))
    (while (agda2-search-hole)
      ;; no body
      (message "found hole")
      )))

(defun agda2-forget-all-goals-pattern ()
  (interactive)
  (progn
    (message "forget all pattern")
    (goto-char (point-min))
    (while (agda2-search-hole-pattern)
      ;; no body
      (message "found hole-pattern")
      )))
