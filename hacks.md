## Variable in trigger cannot appear in both arithmetic and non-arithmetic positions

If you run into something like `forall |i: int| #![trigger gls_next(glb[i], glb[i+1])]  0 <= i < glb.len() - 1 ==> gls_next(glb[i], glb[i+1])`, verus might throw the error 

```
variable `i` in trigger cannot appear in both arithmetic and non-arithmetic positions
```

Verus refuses to assign a trigger and using i+1 breaks being able to use the trigger. I've found the hack to assign another variable j to represent i+1. So we rewrite the above as 

```
    forall |i: int, j: int| #![trigger gls_next(glb[i], glb[j+1])]  0 <= i < glb.len() - 1 && j == i+1 ==> gls_next(glb[i], glb[j])
```
