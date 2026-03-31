local t = {200, 300, 400}
print(table.concat(t))

t[2] = 700
print(table.concat(t))

t.hello = "world"
print(t.hello)

local t2 = {
    polska = "gurom",
    "baguette",
    nil,
    0,
    anotherkey = "anothervalue"
}
for k, v in t2 do
    print(k, v)
end
