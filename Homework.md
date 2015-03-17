# Homeworks #

## Honor Code ##

- Do not copy other's source code, including other students' and resources around the Web. Especially, do not consult with public repositories on software foundations.
- *DO NOT CHEAT*. If you copy other's source code, you will get F. Note that we have a good automatic clone detector.

## Submission ##

- Homework will be issued every Thursday night (Day 0).
- The due is the next Thursday 14:00 (Day 7).
- You can still submit until the next to the next Thursday 14:00 (Day 14), but you will get only 70% of the score.
- Make sure your source code is compiled without error before submission. TA will compile by `make clean; make` in Linux environment. This should not fail.

## Git ##

### How to begin? ###

This is a step-by-step instruction to submit your homework.

- Register at [GitHub](https://github.com).
- Give me your information [here](http://goo.gl/forms/YUjIxNo3LD).
- Apply for [GitHub Education](https://education.github.com)'s [promotion program](https://education.github.com/discount_requests/new).
    + Student, Individual account, 5 free private repositories
- Create a *PRIVATE* repository named `pl2015` in your GitHub namespace.
- Copy the `github.com/snu-sf/pl2015` repository as-is.
    + Important: *DO NOT FORK*. Anybody can see your repository if you fork.
    + This [script](copy-repository.sh) may be helpful to read. If you want to run this script, modify the configuration section in the script.
- Add `jeehoonkang` as a collaborator in your repository (in `Settings` > `Collaborators`).

### How to submit? ###

- Fetch the homework. Run `./fetch-homework.sh` The scirpt is [here](fetch-homework.sh).
- Edit `sf/Assignment??.v`.
- Commit the change by `git add sf/Assignment??.v` and `git commit -m "SUITABLE_MESSAGE"`.
- Push the change to your private repository's `master` branch by `git push`.
- Make sure that your GitHub repository's `master` branch contains your contribution. I will pull your `master` branch at the assignment due.
    + Don't forget to push. I do not believe commit logs, and even though a commit log says it is created before the due date, I will not accept the commit if it is not pushed.
- If anything wrong, first learn Git [here](http://try.github.com/).

### Troubleshooting ###

- In Windows, you can encounter an error `Protocol https not supported or disabled in libcurl` while copying `snu-sf/pl2015.git`. This error is caused by referring `libcurl.dll` in `C:\Windows\SysWOW64`. In that case, you should replace `libcurl.dll` in `C:\Windows\SysWOW64` with `libcurl.dll` in `C:\Users[$USERNAME]\AppData\Local\GitHub`.

### References ###

- If you don't know about Git, start reading articles on [GitHub](https://help.github.com/). Especially, read Bootcamp, Setup, Using Git, User Accounts, and SSH sections.

- For those who are interested, we are going to use the [GitHub's guide to classrom usage](https://education.github.com/guide) and the [sandboxing](https://education.github.com/guide/sandboxing) method.
