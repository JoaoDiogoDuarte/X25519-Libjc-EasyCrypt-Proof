((easycrypt-mode .
  ((eval .
    (cl-flet ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
      (setq easycrypt-load-path `(,(pre ".")))
      (setq easycrypt-prog-args  `("-emacs", "-pp-width", "150",
				   "-R", (pre "../../src")
				   "-R", (pre "../ref4")
				   "-R", (pre "../ref5")
				   "-R", (pre "../mulx")
   				   "-R", (pre "../common")
				   "-R", (pre ".")
				   )
	    )
      )
    ))
))
