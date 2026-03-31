local t = {
    level1 = {
        level2 = {
            level3 = {
                deep = "value"
            }
        }
    }
}
print(t.level1.level2.level3.deep)

local mixed = {
    "first",
    "second",
    nested = {
        "inner1",
        "inner2",
        key = "val"
    }
}
print(mixed[1])
print(mixed[2])
print(mixed.nested[1])
print(mixed.nested.key)

local key = "dynamic"
local t2 = {
    [key] = "found",
    [1 + 1] = "computed",
    ["literal"] = "string"
}
print(t2.dynamic)
print(t2[2])
print(t2.literal)

local outer = {
    inner1 = {a = 1, b = 2},
    inner2 = {c = 3, d = 4}
}
print(outer.inner1.a)
print(outer.inner2.d)

local data = {
    users = {
        {name = "Alice", age = 30},
        {name = "Bob", age = 25}
    }
}
print(data.users[1].name)
print(data.users[2].age)
