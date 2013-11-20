This document contains information on the code released for problem set 4.

Files
=====

 - CHANGELOG.txt, README.txt: documentation
 - Makefile: used to compile the project, see below

 - numbers.ml, geometry.ml, game.ml
     these are the files you must implement for parts 1, 2, and 3 respectively

 - main.ml
     this is where the main entry point to your program is; it sets up and runs
     the tangrams game.  You should change this file to run the
     game with different number implementations

     In our released code, main does not build; you cannot run the interface
     until you have implemented at least one of the NiceField types.  We
     recommend implementing Numbers.Float to start; one you do you should be
     able to run the ui (although it won't be interactive until you implement
     the Game interface).

 - region.mli, region.ml
     this module contains our implementation of the polygon union algorithm.
     You should not need to look at the implementation, but the interface will
     be useful

 - ui.mli, ui.ml
     this file contains our gui.  You should not need to look at or modify these
     files.

 - gltest.ml
     this is a small program for testing your lablgl installation.  See below.

Building and running
====================

We have provided a Makefile that will allow you to build the entire project.
In order to use it, you will need to have the program "make".  This program is
installed by default or available in the package repositories for most
unix-based systems (including MacOS).  It is also available in the cygwin
environment on Windows.

The following commands are available:

make top:
    compile the non-ui code and load it into a toplevel.  This requires rlwrap;
    if you don't want to install it, you can edit the Makefile and remove the
    word "rlwrap" under the "top" section.

make clean:
    remove all generated files

make:
    compiles all of the code and outputs a program called tangrams.  This
    will NOT WORK until you have installed lablgl (see below) and you have
    implemented at least one of the NiceFields.

make gltest:
    generates the program "gltest" which can be used to test your
    lablgl installation 


Our ui depends on a library called lablGL.  This package is available in the
package managers for many linux distributions (I have found it on Ubuntu,
Fedora, and Mint).  You can install it on the virtual machine we have provided
by running the following commands in the terminal:

  opam install lablgl
  sudo apt-get install freeglut-dev libxmu-dev

Zed's password is "password".


Lablgl can be made to work on Windows and MacOS.  Appreciation will be lavished
on anyone who posts clear instructions on Piazza.

