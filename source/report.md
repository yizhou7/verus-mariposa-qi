### Performance of `assert by (nl_airth)`

Depth 2 (trivial), independent polys equations. 
* nlarith mode does not seems to scale well in Verus (w.r.t) Dafny.
* free mode sometimes does not scale very well in Verus/Dafny.

https://github.com/verus-lang/verus/pull/244#issuecomment-1847840158

#### example of 2

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/2/10280999062400484227 

  asserts  auto_verus    free_verus     inst_verus    nlarith_verus    auto_dafny    free_dafny     inst_dafny    nlarith_dafny
---------  ------------  -------------  ------------  ---------------  ------------  -------------  ------------  ---------------
        0  0.00 unsat    0.00 unsat     0.00 unsat    0.00 unsat       0.00 unsat    0.00 unsat     0.00 unsat    0.00 unsat
        1  0.02 unsat    0.02 unsat     0.02 unsat    0.06 unsat       0.02 unsat    0.02 unsat     0.02 unsat    0.02 unsat
        2  0.03 unsat    0.03 unsat     0.03 unsat    1.62 unsat       0.02 unsat    0.02 unsat     0.02 unsat    0.02 unsat
        3  0.03 unsat    0.03 unsat     0.02 unsat    6.33 unsat       0.03 unsat    0.03 unsat     0.03 unsat    0.03 unsat
        4  0.02 unsat    0.03 unsat     0.02 unsat    10.03 timeout    0.03 unsat    0.03 unsat     0.03 unsat    0.03 unsat
        5  0.02 unsat    0.03 unsat     0.03 unsat    10.03 timeout    0.03 unsat    0.03 unsat     0.03 unsat    0.03 unsat
        6  0.03 unsat    0.03 unsat     0.03 unsat    10.03 timeout    0.03 unsat    0.03 unsat     0.02 unsat    0.02 unsat
        7  0.03 unsat    6.38 unsat     0.02 unsat    10.03 timeout    0.03 unsat    7.38 unsat     0.02 unsat    0.02 unsat
        8  0.03 unsat    10.09 timeout  0.02 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.02 unsat    0.02 unsat
        9  0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.02 unsat    0.03 unsat
```

#### summary of 2

```
number of samples 30
number of steps 10
mode             total_unsat    error_free
                       steps         steps
-------------  -------------  ------------
auto_verus             10.00         10.00
free_verus              8.33          8.33
inst_verus             10.00         10.00
nlarith_verus           5.57          5.33
auto_dafny             10.00         10.00
free_dafny              8.33          8.33
inst_dafny             10.00         10.00
nlarith_dafny          10.00         10.00
```

Depth 4 (moderate), independent polys equations. 
* nlarith mode does not seems to scale well in Verus and sometimes in Dafny.
* free mode does not seem to scale well in either Verus/Dafny.

#### example of 4

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/4/2459271600413261222 

  asserts  auto_verus    free_verus     inst_verus    nlarith_verus    auto_dafny    free_dafny     inst_dafny    nlarith_dafny
---------  ------------  -------------  ------------  ---------------  ------------  -------------  ------------  ---------------
        0  0.00 unsat    0.00 unsat     0.00 unsat    0.00 unsat       0.00 unsat    0.00 unsat     0.00 unsat    0.00 unsat
        1  0.02 unsat    0.02 unsat     0.02 unsat    0.02 unsat       0.02 unsat    0.02 unsat     0.02 unsat    0.02 unsat
        2  0.02 unsat    0.02 unsat     0.02 unsat    10.03 timeout    0.02 unsat    0.02 unsat     0.02 unsat    0.03 unsat
        3  0.02 unsat    0.07 unsat     0.02 unsat    10.03 timeout    0.03 unsat    0.07 unsat     0.02 unsat    0.27 unsat
        4  0.03 unsat    5.98 unsat     0.02 unsat    10.03 timeout    0.03 unsat    6.88 unsat     0.02 unsat    0.06 unsat
        5  0.03 unsat    10.09 timeout  0.02 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.02 unsat    0.06 unsat
        6  0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout
        7  0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout
        8  0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.03 unsat    0.07 unsat
        9  0.03 unsat    10.08 timeout  0.03 unsat    10.03 timeout    0.03 unsat    10.09 timeout  0.03 unsat    10.03 timeout
```

#### summary of 4

```
number of samples 30
number of steps 10
mode             total_unsat    error_free
                       steps         steps
-------------  -------------  ------------
auto_verus             10.00         10.00
free_verus              4.77          4.77
inst_verus             10.00         10.00
nlarith_verus           2.73          2.73
auto_dafny             10.00         10.00
free_dafny              4.67          4.67
inst_dafny             10.00         10.00
nlarith_dafny           9.33          9.13
```

Depth 6 (moderate), independent polys equations. 
* free mode removed
* nlarith mode does not seems to scale well in either Verus or Dafny.

#### example of 6

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/6/16703716602383634820 

  asserts  auto_verus    inst_verus    nlarith_verus    auto_dafny    inst_dafny    nlarith_dafny
---------  ------------  ------------  ---------------  ------------  ------------  ---------------
        0  0.00 unsat    0.00 unsat    0.00 unsat       0.00 unsat    0.00 unsat    0.00 unsat
        1  0.02 unsat    0.02 unsat    0.02 unsat       0.02 unsat    0.02 unsat    0.02 unsat
        2  5.22 unsat    0.02 unsat    0.03 unsat       0.03 unsat    0.02 unsat    0.02 unsat
        3  0.03 unsat    0.02 unsat    10.03 timeout    0.03 unsat    0.02 unsat    0.02 unsat
        4  0.03 unsat    0.03 unsat    10.03 timeout    0.03 unsat    0.02 unsat    0.02 unsat
        5  0.03 unsat    0.03 unsat    10.03 timeout    0.03 unsat    0.02 unsat    0.03 unsat
        6  0.03 unsat    0.03 unsat    10.03 timeout    0.03 unsat    0.03 unsat    10.03 timeout
        7  0.03 unsat    0.03 unsat    10.03 timeout    0.03 unsat    0.03 unsat    10.03 timeout
        8  0.03 unsat    0.03 unsat    10.03 timeout    0.06 unsat    0.03 unsat    10.03 timeout
        9  0.06 unsat    0.03 unsat    10.03 timeout    0.06 unsat    0.03 unsat    10.03 timeout
```

#### summary of 6

```
number of samples 30
number of steps 10
mode             total_unsat    error_free
                       steps         steps
-------------  -------------  ------------
auto_verus             10.00         10.00
inst_verus             10.00         10.00
nlarith_verus           3.40          3.40
auto_dafny             10.00         10.00
inst_dafny             10.00         10.00
nlarith_dafny           5.57          5.33
```

### Exponential (?) Growth Independent `assert by`

### Spike in Second `assert by`

Depth 8 (complex), independent polys equations. 
* Exponential growth in time, despite independence
* Sometimes there is a sudden bump in verification time at step 2, then decreases.

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/8/11408320289042858979
```

<img src="mariposa_data/8/11408320289042858979/log.png" width="600" height="600" />

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/8/12402304884678657734
```

<img src="mariposa_data/8/12402304884678657734/log.png" width="600" height="600" />

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/8/4116775489050393195
```

<img src="mariposa_data/8/4116775489050393195/log.png" width="600" height="600" />

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/8/5233501277902642195
```

<img src="mariposa_data/8/5233501277902642195/log.png" width="600" height="600" />

```
python3 tools/mariposa_nlqi/plotter.py mariposa_data/8/5644133508364908149
```

<img src="mariposa_data/8/5644133508364908149/log.png" width="600" height="600" />


