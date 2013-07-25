((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(setq coq-prog-name (expand-file-name "../HoTT/hoqtop"))
			(setq coq-load-path `((,(expand-file-name ".") "HoTT.Categories")
					      (,(expand-file-name "../HoTT/theories") "HoTT"))))))))
