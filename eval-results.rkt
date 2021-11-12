#lang racket
        

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

(define (output-macro-results output-port content)
  (define vanilla-lengths (get-sum content fourth))
  (define greedy-lengths (get-sum content fifth))
  (fprintf output-port "~s" (list vanilla-lengths greedy-lengths)))

(module+ main
  (command-line #:program "report"
                #:args (results-file macro-output-file)
    (output-macro-results (open-output-file macro-output-file #:exists 'replace)
                          (file->list results-file))))