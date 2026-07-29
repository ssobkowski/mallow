local funcs = {
    add = function(a, b) return a + b end,
    multiply = function(a, b) return a * b end
}
print(funcs.add(2, 3))
print(funcs.multiply(4, 5))

local arr_funcs = {
    function() return "first" end,
    function() return "second" end
}
print(arr_funcs[1]())
print(arr_funcs[2]())

local with_nil = {a = 1, b = 2}
print(with_nil.a)
print(with_nil.missing) -- nil
print(with_nil.b)

local special = {
    1,
    "string",
    true,
    false,
    func = function() return 99 end,
    nested = {x = 10}
}
print(special[1])
print(special[2])
print(special[3])
print(special[4])
print(special.func())
print(special.nested.x)

local nums = {
    inf = math.huge,
    neginf = -math.huge,
    zero = 0,
    negzero = -0
}
print(nums.inf)
print(nums.neginf)
print(nums.zero)
print(nums.negzero)

local circular = {a = 1}
circular.self = circular
print(circular.a)
print(circular.self.a)
print(circular.self.self.a)
