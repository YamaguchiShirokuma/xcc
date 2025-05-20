#!/bin/csh -f
set noglob
set num = 0
set bad = 0
foreach line (`cat testcase2.txt`)
    @ num++
    set x = `echo $line | awk 'BEGIN{FS=","}{print $1, $2}'`
    ./a.out $x[1] > foo.s
    gcc -o b.out foo.s
    set result=`./b.out`
    if ($result != $x[2]) then
	echo $x[1], $x[2], bad result\!\! $result
	@ bad++
    endif
end
echo num = $num, bad = $bad
unset noglob
