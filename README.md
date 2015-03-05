# SNU 4190.310, 2015 Spring #

- Instructor: Prof. [Gil Hur](http://sf.snu.ac.kr/gil.hur)
- TA: [Jeehoon Kang](http://sf.snu.ac.kr/jeehoon.kang)
    + Email address: [pl2015@sf.snu.ac.kr](mailto:pl2015@sf.snu.ac.kr).
        * Send emails for personal matters only. Use the issue tracker.
        * DO NOT send emails to jee...@sf.snu.ac.kr.
        * In the case you send TA an email, specify your name and your student ID.
    + Office Hour: Please email me to make an appointment.

## Announcements ##

- We will have a lab session at 2015/03/04 (Thu). Please come to Software Lab, 3rd floor, bldg 302.

## Homeworks ##

| Due        	| Description 	 	 	 	 	 	 	 	 	 	 	 	 	 	| Notes 	|
|------------	|---------------------------------------------------------------	|-------	|
| 2015/03/09 	| Register at [GitHub](https://github.com), and give me your information [here](http://goo.gl/forms/YUjIxNo3LD).	|       	|
| 2015/03/09 	| Read articles on [GitHub](https://help.github.com/). Especially, read Bootcamp, Setup, Using Git, User Accounts, and SSH sections.	|       	|
| 2015/03/09 	| Be ready to do homework and submit it.	|       	|

## Must Read ##

- *READ CAREFULLY* this section.

### Grading ###

- Homework: 40%
    + Coq problems in the [software foundations material](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html). Read carefully the next subsections.
- Exams: 50% (mid-term 25% and final 25%)
    + You will solve Coq problems at the lab during the exam.
- Attendance: 10%
    + -2% per absence. -1% per too-late-coming. From 2015/03/09. *IMPORTANT: -11% makes an F*.
    + You will be assigned a seat that you will use in this course (2015/03/05).
    + TA will take two pictures for every class, at the middle and at the end. Then TA will grade attendance automatically.

### Questions ###

- In class: if you speak Korean, ask in Korean. Otherwise, ask in English.
- In the [GitHub repository issue tracker](https://github.com/snu-sf/pl2015/issues): ask in English.
- Send email for *personal matters only*.

### Software ###

- Use designated versions of software in this class to avoid version incompatibility. Your submission will not be properly graded if you do not follow this instruction.
- Use [Coq 8.4pl5](https://coq.inria.fr/distrib/V8.4pl5/files/).
    + Coq is already installed in the lab.
    + For your personal computer:
        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.01.0.
        * Download [tarball](https://coq.inria.fr/distrib/V8.4pl5/files/coq-8.4pl5.tar.gz) file.
        * Extract the tarball, `./configure`, `make`, and then `make install`.
        * Test by `coqc -v` in the command line. Check your `PATH` variable if you get an error.
    + For OS X, I recommend you to download [those with CoqIDE bundle](https://coq.inria.fr/distrib/V8.4pl5/files/coqide-8.4pl5.dmg). And you may have to properly set path variable. add the following in `~/.bashrc`: `export PATH=/Applications/CoqIdE_8.4pl5.app/Resources/bin/:$PATH`. (May not work in your environment; be cautious before blindly adding the line.)
    + For OS X, an alternative way to install Coq is using `brew`. See #1 for more details.
- Use software foundations material in this repository (as explained in the Homeworks section below).

### Homeworks ###

See [Homework.md](Homework.md) for more details.

## Misc. ##

- [Student IDs (TA only)](https://docs.google.com/a/sf.snu.ac.kr/spreadsheets/d/12lKRN2n9trryDC3JZSGsyo2JSeTQUoDy1BU2vArtcVA/edit#gid=937947926)
