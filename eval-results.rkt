#lang racket

(require "eval-library.rkt")
(require plot/no-gui)

(define (getter symbol)
  (define m
    (make-hash `((proof-length . ,fourth)
                (greedy-proof-length . ,fifth)
                 (dag-size . ,sixth)
                 (greedy-dag-size . ,seventh))))
  (hash-ref m symbol))

(define (output-results-with-tag output-port content tag getter-normal getter-greedy length-str)
  (define (output name val #:output-percent [output-percent #f])
    (output-latex-macro (string-append length-str "-" name "-" tag) val output-port #:output-percent output-percent))
  (define vanilla-lengths (get-sum content (getter getter-normal)))
  (define greedy-lengths (get-sum content (getter getter-greedy)))

  
  (define num-smaller (get-sum content
                               (lambda (row)
                                 (if (> ((getter getter-normal) row)
                                        ((getter getter-greedy) row))
                                     1 0))))
  (define num-smaller-than-half
    (get-sum content
             (lambda (row)
               (if (> ((getter getter-normal) row)
                      (* 2 ((getter getter-greedy) row)))
                   1 0))))
  
  (output "vanilla-sum" vanilla-lengths)
  (output "greedy-sum" greedy-lengths)
  (output "percent-greedy-smaller-than-vanilla" (/ num-smaller (length content))
          #:output-percent #t)
  (output "percent-greedy-smaller-than-half-vanilla" (/ num-smaller-than-half (length content))
          #:output-percent #t)
  (output "percent-greedy-reduction" (/ (- vanilla-lengths greedy-lengths) vanilla-lengths)
          #:output-percent #t))

(define (output-macro-results output-port content getter-normal getter-greedy length-str)
  (define filtered-greater-than-10
    (filter (lambda (row) (> ((getter getter-normal) row) 10)) content))
  (define filtered-greater-than-50
    (filter (lambda (row) (> ((getter getter-normal) row) 50)) content))
  (output-results-with-tag output-port content "" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-10 "length-grt-10" getter-normal getter-greedy length-str)
  (println "" output-port)
  (output-results-with-tag output-port filtered-greater-than-50 "length-grt-50" getter-normal getter-greedy length-str))

(define (make-proof-len-scatter output-file cutoff results getter-normal getter-greedy length-str)
  (define scatter-points (points
                          #:alpha 0.1
                          #:color "blue"
                          #:size 2
                          #:x-max cutoff
                          #:y-max cutoff
                          
                  (list->vector
                  (map (lambda (row)
                        (vector ((getter getter-normal) row)
                                ((getter getter-greedy) row)))
                      results))))

  (parameterize-plot-size
   300
   1
   ""
   (string-append "Unoptimized Proof " length-str)
   (string-append "Greedily Optimized Proof " length-str)
   output-file
   (lambda ()
     (plot-pict
      scatter-points))))

(module+ main
  (command-line #:program "report"
                #:args (results-file report-dir)
    (define macro-output-file (build-path report-dir "macros.txt"))
    (define results (file->list results-file))
    (define macro-port (open-output-file macro-output-file #:exists 'replace))
    (output-macro-results macro-port
                          results 'proof-length 'greedy-proof-length "proof-length")
    (println "" macro-port)
    (output-macro-results macro-port
                          results 'dag-size 'greedy-dag-size "dag-size")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter.png") #f results 'proof-length 'greedy-proof-length "Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed800.png") 800 results 'proof-length 'greedy-proof-length "Lengths")
    (make-proof-len-scatter (build-path report-dir "proof-len-scatter-zoomed200.png") 200 results 'proof-length 'greedy-proof-length "Lengths")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter.png") #f results 'dag-size 'greedy-dag-size "DAG size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed800.png") 800 results 'dag-size 'greedy-dag-size "DAG size")
    (make-proof-len-scatter (build-path report-dir "dag-size-scatter-zoomed200.png") 200 results 'dag-size 'greedy-dag-size "DAG size")

    
  )
  )