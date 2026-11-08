# Scratch CAS 核心

纯 Scratch 积木实现的符号计算内核

函数式命令：
- simplify(表达式)
- expand(表达式)
- diff(表达式[, 变量])        默认变量 x
- subst(表达式, 变量=表达式)   符号代入
- help

裸表达式会自动化简：
```
1+1                                ->  2
0                                  ->  0
1/0                                ->  oo
```
示例：
```
simplify(x+2*x)                    ->  3*x
simplify(sin(x+y)^2+cos(y+x)^2)    ->  1
expand((x+1)^3)                    ->  x^3 + 3*x^2 + 3*x + 1
diff(sin(x^2))                     ->  2*cos(x^2)*x
diff(y,y)                          ->  1
diff(5^x)                          ->  ln(5)*5^x
diff(x^x)                          ->  (ln(x) + 1)*x^x
diff(x^2.5)                        ->  5/2*x^(3/2)
sqrt(0)                            ->  0
sqrt(8)                            ->  2*sqrt(2)
sqrt(9)                            ->  3
sqrt(8/9)                          ->  2/3*sqrt(2)
sqrt(x)^4                          ->  x^2
expand((x+1)^10)                   ->  x^10 + 10*x^9 + ... + 1
gcd(x^3+y^3,x^5+y^5)               ->  x + y
simplify((x^3+y^3)/(x^5+y^5))      ->  (x^2 - x*y + y^2)/(x^4 - ... + y^4)
sqrt(x)^6                          ->  x^3
sqrt(x)^3                          ->  sqrt(x)*x
diff(sqrt(x)^4)                    ->  2*x
ln(exp(x))                         ->  x
exp(ln(x))                         ->  x
abs(abs(x))                        ->  abs(x)
subst(x^2, x=(a+1))                ->  (a + 1)^2
subst(x^2 + 2*x + 1, x=3)        ->  16
```
嵌套调用：
```
simplify(subst(x^2, x=(a+1)))      ->  (a + 1)^2
diff(subst(x^2, x=(a+1)), a)       ->  2*(a + 1)
```
