# John H. Conway's M13.

In 1987, mathematician [John Horton Conway](https://en.wikipedia.org/wiki/John_Horton_Conway) discovered an algebraic structure that he named [M13](https://en.wikipedia.org/wiki/Mathieu_groupoid). It is a lesser cousin of the sporadic finite simple group [M12](https://en.wikipedia.org/wiki/Mathieu_group_M12), discovered by Émile Léonard Mathieu in 1861. Like its cousin, M13 is of considerable symmetric beauty but, Alas!, it wasn't born a group.

Nevertheless, John Conway liked to play with M13, and that is how it was introduced: as a game.

### The Structure, the Game, and ...

For a description of M13, the structure and the game, `Java_applet_1997/info.html` is my original description from 1997.

Alternatively, you might like Lieven de Buyn's 2007 description from his [his blog](http://www.neverendingbooks.org/conways-puzzle-m13).

There is also a short entry in [Wikipedia](https://en.wikipedia.org/wiki/Mathieu_groupoid).

### ... the Java Applet

In 1997, during the final days of my graduate studies, M13 was brought to my attention by my thesis supervisor Thomas Beth. At that time, my colleague Markus Püschel and me had studied quite a number of permutation-based games, including Rubik's cube and Sam Loyd's 15-puzzle, and developed algorithms for constructing shorter solutions. And so it came that I quickly created an interactive version of the M13 game where you can click the puzzle pieces to solve it manually, or you watch our solution algorithm do the trick.

The program for constructing the solution algorithm from a com pact mathematical description of the puzzle was written in [GAP](https://en.wikipedia.org/wiki/GAP_\(computer_algebra_system\)), Version 3.4 at the time. GAP is a Computer Algebra system which knows a lot about finite groups, including the [Schreier-Sims algorithm](https://en.wikipedia.org/wiki/Schreier–Sims_algorithm) for computing [Strong Generating Sets](https://en.wikipedia.org/wiki/Strong_generating_set). We then exported the tables constructed in GAP to Java or C syntax. The source code is in `src/GAP3`.

The interactive game for M13 is written in Java, Version 1.0 at the time, implementing a [Java applet](https://en.wikipedia.org/wiki/Java_applet) to be run in any major web browser. The entire source code is `src/Java/M13.java`, consisting of 1530 lines of (ancient) code. It was a one-line change to port the source from Java 1.0 (January 1996) to a modern version, Java SE 8 (LTS). You can compile it with `java -g M13.java`.

But don't expect any browser to run a Java applet, these days (2020). However, the `appletviewer` stand-alone app, included in your favourite JDK, does. Try this command in the `Java_applet_1997` directory:

```
appletviewer index.html
```

To play, click `scramble` then click numbered discs to make moves. The slider above the buttons controls the speed of movement.

Have fun!

_Sebastian_

### References:

1. John H. Conway. _Graphs and groups and M13._ In Notes from New York Graph Theory Day XIV, pages 18–29, 1987.

2. John H. Conway. _M13._ In Surveys in combinatorics, 1997 (London), volume 241 of London Mathematical Society Lecture Note Series, pages 1–11. Cambridge University Press, Cambridge, 1997.

3. Sebastian Egner and Markus Püschel. _Solving Puzzles related to Permutation Groups._ ISSAC Conference, Rostock 1998.

4. Sebastian Egner, Thomas Beth. _How to Play M 13?._ Designs, Codes and Cryptography 16, pages 243–247, 1999. 

5. John H. Conway, Noam D. Elkies, and Jeremy L. Martin. [_The Mathieu Group M12 and its Pseudogroup Extension M13._](https://arxiv.org/pdf/math/0508630.pdf) Arxiv.org, 2005. 

6. Lieven de Bruyn. [_The Mathieu groupoid (1)._](http://www.neverendingbooks.org/the-mathieu-groupoid-1) his blog, 2007.
