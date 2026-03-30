local mixed = {
    [1] = "numeric 1",
    ["1"] = "string 1",
    [true] = "bool true",
    [false] = "bool false",
    key = "string key"
}
for k, v in pairs(mixed) do
    print(type(k), k, v)
end

local floats = {}
floats[1.0] = "one"
floats[2.5] = "two point five"
floats[3.0] = "three"
print(floats[1])
print(floats[2.5])
print(floats[3])

local strkeys = {
    ["123"] = "looks numeric",
    ["abc"] = "letters",
    ["true"] = "looks boolean"
}
print(strkeys["123"])
print(strkeys.abc)
print(strkeys["true"])
