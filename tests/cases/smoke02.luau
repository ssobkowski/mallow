local t = { 1, 2, 3 }
local i = 1
t[i], i = i + 10, i + 1
-- rhs: i+10=11, i+1=2, both with i=1
print(t[1])
print(i)
