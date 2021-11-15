#lang racket

(require "eval-library.rkt")
(require plot/no-gui)

(define (getter symbol)
  (define m
    (make-hash `((proof-length . ,fourth)
                (greedy-proof-length . ,fifth))))
  (hash-ref m symbol))

(define (output-results-with-tag output-port content tag)
  (define (output name val #:output-percent [output-percent #f])
    (output-latex-macro (string-append name "-" tag) val output-port #:output-percent output-percent))
  (define vanilla-lengths (get-sum content (getter 'proof-length)))
  (define greedy-lengths (get-sum content (getter 'greedy-proof-length)))

  
  (define num-smaller (get-sum content
                               (lambda (row)
                                 (if (> ((getter 'proof-length) row)
                                        ((getter 'greedy-proof-length) row))
                                     1 0))))
  (define num-smaller-than-half
    (get-sum content
             (lambda (row)
               (if (> ((getter 'proof-length) row)
                      (* 2 ((getter 'greedy-proof-length) row)))
                   1 0))))
  
  (output "vanilla-proof-lengths-sum" vanilla-lengths)
  (output "greedy-proof-lengths-sum" greedy-lengths)
  (output "percent-greedy-smaller-than-vanilla" (/ num-smaller (length content))
          #:output-percent #t)
  (output "percent-greedy-smaller-than-half-vanilla" (/ num-smaller-than-half (length content))
          #:output-percent #t)
  (output "percent-greedy-reduction-proof-size" (/ (- vanilla-lengths greedy-lengths) vanilla-lengths)
          #:output-percent #t))

(define (output-macro-results output-port content)
  (define filtered-greater-than-10
    (filter (lambda (row) (> ((getter 'proof-length) row) 10)) content))
  (define filtered-greater-than-50
    (filter (lambda (row) (> ((getter 'proof-length) row) 50)) content))
  (output-results-with-tag output-port content "")
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-10 "length-grt-10")
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-50 "length-grt-50"))

(define (make-proof-len-scatter output-file cutoff results)
  (define scatter-points (points
                          #:alpha 0.1
                          #:color "blue"
                          #:size 2
                          #:x-max cutoff
                          #:y-max cutoff
                          
                  (list->vector
                  (map (lambda (row)
                        (vector ((getter 'proof-length) row)
                                ((getter 'greedy-proof-length) row)))
                      results))))

  (parameterize-plot-size
   300
   1
   ""
   "Unoptimized Proof Lengths"
   "Greedily Optimized Proof Lengths"
   output-file
   (lambda ()
     (plot-pict
      scatter-points))))

(module+ main
  (command-line #:program "report"
                #:args (results-file macro-output-file proof-len-scatter-file proof-len-zoomed800 proof-len-zoomed200)
    (define results (file->list results-file))
    (output-macro-results (open-output-file macro-output-file #:exists 'replace)
                          results)
    (make-proof-len-scatter proof-len-scatter-file #f results)
    (make-proof-len-scatter proof-len-zoomed800 800 results)
    (make-proof-len-scatter proof-len-zoomed200 200 results)
  )
  )