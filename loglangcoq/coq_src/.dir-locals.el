((nil
  . ((eval
      . (progn 
	  ;; coccinelle root directory (ending with slash)
	  (let* ((project-root-directory
		  (or (locate-dominating-file buffer-file-name ".dir-locals.el") ".")))
                  	    (setq compile-command (concat "make -C " project-root-directory))
              )))))
