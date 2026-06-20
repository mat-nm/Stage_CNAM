((nil
  . ((eval
      . (progn 
	  (let* ((project-root-directory
		  (locate-dominating-file buffer-file-name ".dir-locals.el"))
		  (genenv-root-directory
		   (concat project-root-directory "/coq_src/lib/Generic_Env_v0.3")))
	    ;; coccinelle tags file and coq debugger executable
	    ;;(setq tags-file-name (concat coccinelle-root-directory "TAGS"))
	    ;; Setting the compilation directory to coccinelle root.
	    (setq compile-command (concat "make -C " project-root-directory))
	    (setq coq-load-path `(,genenv-root-directory))
            ))))))
