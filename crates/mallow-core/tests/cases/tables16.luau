local t = {}
t[t] = 1
print(t[t])

local u = {}
u.x = #u
print(u.x)

local v = {}
v[1] = #v
print(v[1])
