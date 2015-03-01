# SNU 4190.310, 2015 Spring #

- Instructor: Prof. [Gil Hur](http://sf.snu.ac.kr/gil.hur)
- TA: [Jeehoon Kang](http://sf.snu.ac.kr/jeehoon.kang)
    + Email address: [pl2015@sf.snu.ac.kr](mailto:pl2015@sf.snu.ac.kr).
        * Send emails for personal matters only. Use the issue tracker.
        * DO NOT send emails to jee...@sf.snu.ac.kr.
        * Give me your name and your student ID in emails.
    + Office Hour: [TBA](http://en.wikipedia.org/wiki/To_be_announced)

## Homeworks ##

| Due        	| Description 	 	 	 	 	 	 	 	 	 	 	 	 	 	| Notes 	|
|------------	|---------------------------------------------------------------	|-------	|
| 2015/03/09 	| Give me your information [here](http://goo.gl/forms/YUjIxNo3LD).	|       	|
| 2015/03/09 	| Read articles on [GitHub](https://help.github.com/).          	|       	|

## Must Read ##

- *READ CAREFULLY* this article.

### Software ###

- Use designated versions of software in this class to avoid version incompatibility. Your submission will not be properly graded if you do not follow this instruction.
- Use [Coq 8.4pl4](https://coq.inria.fr/distrib/V8.4pl4/files/).
    + Coq is already installed in the lab.
    + For your personal computer:
        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.01.0.
        * Download [tarball](https://coq.inria.fr/distrib/V8.4pl4/files/coq-8.4pl4.tar.gz) file.
        * Extract the tarball, `./configure`, `make`, and then `make install`.
        * Test by `coqc -v` in the command line.
    + For OS X, I recommend you to download [those with CoqIDE bundle](https://coq.inria.fr/distrib/V8.4pl4/files/coqide-8.4pl4.dmg). And you may have to properly set path variable. add the following in `~/.bashrc`: `export PATH=/Applications/CoqIdE_8.4pl4.app/Resources/bin/:$PATH`. (May not work in your environment; be cautious before blindly adding the line.)
- Use software foundations material in this repository (as explained in the Homeworks section below).

### Homeworks ###

- Honor code: do not copy other's source code, including other students' and resources around the Web. Especially, do not consult with public repositories on software foundations.
    + *DO NOT CHEAT*. If you copy other's source code, you will get F. Note that we have a good automatic clone detector.
- Make sure your source code is compiled without error before submission. TA will compile by `make clean; make` in Linux environment. This should not fail.
- On submission (TODO)

### Questions ###

- Ask question in the [GitHub repository issue tracker](https://github.com/snu-sf/pl2015/issues).

## Misc. ##

- [Student IDs (TA only)](https://docs.google.com/a/sf.snu.ac.kr/spreadsheets/d/12lKRN2n9trryDC3JZSGsyo2JSeTQUoDy1BU2vArtcVA/edit#gid=937947926)
