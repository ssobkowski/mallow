local original = {a = 1, b = 2, c = 3}
local copy = {}
for k, v in pairs(original) do
    copy[k] = v
end
print(original.a, copy.a)
original.a = 999
print(original.a, copy.a)

local t1 = {x = 10}
local t2 = t1
print(t1.x, t2.x)
t1.x = 20
print(t1.x, t2.x)

local a = {1, 2, 3}
local b = {1, 2, 3}
local c = a
print(a == b)
print(a == c)

local inner = {data = "shared"}
local outer1 = {nested = inner}
local outer2 = {nested = inner}
print(outer1.nested.data)
print(outer2.nested.data)
inner.data = "modified"
print(outer1.nested.data)
print(outer2.nested.data)

local parent = {child = {x = 1}}
local shallow = {}
for k, v in pairs(parent) do
    shallow[k] = v
end
parent.child.x = 999
print(shallow.child.x)
