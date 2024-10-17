# Action Codes in Coq

Coq formalization of the following ICALP23 paper:

  * **Paper:** [Action Codes](https://drops.dagstuhl.de/opus/volltexte/2023/18189/) ([Frits Vaandrager](http://www.cs.ru.nl/F.Vaandrager/), [Thorsten Wißmann](https://thorsten-wissmann.de/)): 50th International Colloquium on Automata, Languages, and Programming, ICALP 2023.
   [DOI: 10.4230/LIPIcs.ICALP.2023.137](https://dx.doi.org/10.4230/LIPIcs.ICALP.2023.137)
  * **Preprint/Appendix:** The preprint with all appendices can be found on https://arxiv.org/abs/2301.00199
  * **ICALP23 talk:** [pdf slides](https://thorsten-wissmann.de/talks/wissmann-icalp23-slides.pdf)


## Online Documentation

  - The up-to-date generated **coq doc** is on gitlab pages: https://twissmann.pages.science.ru.nl/action-codes-coq/
  - The version described in the ICALP 2023 paper is the commit [tagged `icalp23`](https://gitlab.science.ru.nl/twissmann/action-codes-coq/-/tags/icalp23). The coq doc for this version is [permanently archived here](https://thorsten-wissmann.de/archive/action-codes-icalp23/)


## Compilation

In order to compile the source files (i.e. check the proofs), run:

    coq_makefile -f _CoqProject -o Makefile
    make

The sources compiled in May 2023 with Coq 8.16.1 and OCaml 4.14.0

