#lang racket

(provide file->list get-sum parameterize-plot-size output-latex-macro latex-output-percent latex-format-item output-latex-table)
(require plot/no-gui pict)

(define global-plot-scale 2)
(define numbers-size 10)
(define labels-size 12)

(define (output-latex-table rows port)
  
  (fprintf port "\\begin{tabular}{|c | ~a|}\n \\hline \n" (apply string-append (make-list (- (length (first rows)) 1) "c ")))
  (for ([row rows])
       (fprintf port "~a \\\\\n" (string-join (map latex-format-item  row) " & ")))
  

  (fprintf port "\\end{tabular}"))
  

(define (output-latex-macro name val port [comment ""] #:output-percent [output-percent #f])
  (define comment-string
    (if (equal? comment "")
        ""
        (format "% ~a" comment)))
  (fprintf port "\\newcommand{\\~a}{~a\\xspace}~a\n" name (latex-format-item val #:output-percent output-percent)
           comment-string))

(define (get-substrings-divisible str n)
  (cond
    [(equal? (string-length str) n)
     (list str)]
    [else
      (cons (substring str 0 n) (get-substrings-divisible (substring str n) n))]))

(define (get-substrings str n)
  (define head (substring str 0 (modulo (string-length str) n)))
  (define tail (substring str (modulo (string-length str) n)))
  (cond
    [(equal? (string-length tail) 0)
     (list head)]
    [(equal? (string-length head) 0)
     (get-substrings-divisible tail n)]
    [else
     (cons head (get-substrings-divisible tail n))]))

(define (insert-thinspaces string space)
  (string-join (get-substrings string 3) space))

(define (round1 num)
  (~r num #:precision `(= 1)))

(define (latex-output-percent proportion)
  (format "~a\\%"
          (round1 (* 100 proportion))))

(define (latex-format-item item #:output-percent [output-percent #f])
  (cond
    [output-percent
     (latex-output-percent item)]
    [(string? item)
     item]
    [(exact-integer? item)
     (insert-thinspaces (format "~a" item) "\\thinspace")]
    [else (format "~a" (~r item #:precision `(= 2)))]))

(define (file->list file)
  (define port (open-input-file file))
  (define all empty)
  (let loop ([content (read port)])
    (when (not (equal? content eof))
          (set! all (cons content all))
          (loop (read port))))
  (reverse all))

(define (get-sum content getter)
  (apply + (map getter content)))

(define (parameterize-plot-size width scale-width title bottom-axis left-axis output-file func)
  (define actual-w
    (inexact->exact (floor (* width global-plot-scale))))
  ;; increase font size so that when it is scaled down into the latex pdf, it is the correct size
  (define f-size (inexact->exact (floor (* global-plot-scale numbers-size (/ width 400) (/ 1.0 scale-width)))))
  (define graph-pict
    (parameterize ([plot-width actual-w]
                   [plot-height (inexact->exact
                                 (floor (* 300 global-plot-scale)))]
                   [plot-x-label #f]
                   [plot-y-label #f]
                   [plot-font-size
                    f-size])
      (func)))
  (define font-pixel-height (inexact->exact (floor (* global-plot-scale labels-size (/ width 400) (/ 1.0 scale-width)))))
  (define title-pict
    (if (equal? title "")
        (filled-rectangle 0 0)
        (text title "Computer Modern"
              font-pixel-height)))
  (define left-pict
    (if (equal? left-axis "")
        (filled-rectangle 0 0)
        (text left-axis "Computer Modern"
              font-pixel-height (/ pi 2))))
  (define bottom-pict
    (if (equal? bottom-axis "")
        (filled-rectangle 0 0)
        (text bottom-axis "Computer Modern"
              font-pixel-height)))
  (define space-block (colorize (filled-rectangle (pict-height title-pict)
                                                  (pict-height title-pict)) "white"))

  (define without-background
    (hc-append left-pict space-block
               (vc-append title-pict
                          space-block
                          (vc-append
                           graph-pict
                           space-block
                           bottom-pict))))

  (define res
    (lt-superimpose
     (colorize (filled-rectangle (pict-width without-background) (pict-height without-background)) "white")
     without-background))

  (send (pict->bitmap res) save-file output-file 'png))