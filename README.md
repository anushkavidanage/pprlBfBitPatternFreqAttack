Efficient Cryptanalysis of Bloom Filters for PPRL
====================================================

Peter Christen, Rainer Schnell, Dinusha Vatsalan, and Thilina Ranbaduge

Paper title: Efficient Cryptanalysis of Bloom Filters for Privacy-Preserving Record Linkage\
Paper URL: [here](https://link.springer.com/chapter/10.1007/978-3-319-57454-7_49)

Copyright 2017 Australian National University and others.
All Rights reserved.

See the file COPYING for the terms under which the computer program
code and associated documentation in this package are licensed.

22 February 2023.

Contact: peter.christen@anu.edu.au, anushka.vidanage@anu.edu.au

-------------------------------------------------------------------

Requirements:
=============

The Python programs included in this package were written and
tested using Python 2.7.6 running on Ubuntu 16.04

The following extra packages are required:
- numpy
- bitarray

Running the attack program:
===========================

To run the program, use the following command (with an example setting):

  python bf_attack_bit_pattern_freq.py 2 rh 15 1000 none clk True 100 [100,50,20,10] 
         path-to-encode-dataset.csv.gz 0 , True [1,2,8] path-to-plaintext-dataset.csv.gz 
         0 , True [1,2,8] None None

For moe details about the command line arguments see comments at the top of 
'bf_attack_bit_pattern_freq.py'
