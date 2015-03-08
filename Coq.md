# Coq #

## Software ##

Use designated versions of software in this class to avoid version incompatibility. Your submission will not be properly graded if you do not follow this instruction.
- Use [Coq 8.4pl5](https://coq.inria.fr/distrib/V8.4pl5/files/).
    + Coq is already installed in the lab.
    + For Linux:
        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.01.0.
        * Install `libgtk2` by `sudo apt-get install libgtk2.0-dev` or `sudo yum install gtk2-devel`.
        * Install lablgtk2 by `opam install lablgtk`
        * Download [tarball](https://coq.inria.fr/distrib/V8.4pl5/files/coq-8.4pl5.tar.gz) file.
        * Extract the tarball, `./configure -coqide opt`, `make`, and then `make install`.
        * Test by `coqc -v` in the command line. Check your `PATH` variable if you get an error.
        * Run CoqIDE by `coqide`.
    + For Windows / OS X, I recommend you to download those with CoqIDE bundle ([for Windows](https://coq.inria.fr/distrib/V8.4pl5/files/coq-installer-8.4pl5.exe) or [for OS X](https://coq.inria.fr/distrib/V8.4pl5/files/coqide-8.4pl5.dmg)).
        * In OS X, at first run, you may see an error message saying "Failed to load coqtop." Then click "No", and then find `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop` and open for once. Then goto `CoqIDE` > `Preferences` > `Externals`. And then change `coqtop` into `/Applications/CoqIDE_8.4pl5.app/Contents/Resources/bin/coqtop`.
    + For OS X, an alternative way to install Coq is using `brew`. See [#1](https://github.com/snu-sf/pl2015/issues/1) for more details.
- Use software foundations material in this repository (as explained in the Homeworks section below).
