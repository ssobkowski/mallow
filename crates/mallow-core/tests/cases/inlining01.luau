local function side_effect(label)
    print(label)
    return label
end

local function noinline_eval_order()
    -- must NOT inline; changes evaluation order
    -- inlining `x` would evaluate f() before g() instead of f() then g()
    -- causing wrong print order
    local x = side_effect("A")
    return side_effect("B"), x
end

local function noinline_duplicate_exec()
    -- must NOT inline; duplicates execution
    -- inlining would call f() on every loop iteration instead of once
    local i = 0
    local function iter()
        i += 1
        return i <= 3
    end

    local x = iter()
    local n = 0
    while x do
        n += 1
        x = iter()
    end
    return n
end

local function noinline_nested_call()
    -- must NOT inline; nested call moves f()
    -- inlining `x` would move side_effect("A") inside side_effect("B")'s argument
    -- changing call order
    local x = side_effect("C")
    return side_effect("D") .. x
end

local function may_inline()
    -- may inline
    local x = 42
    return x
end

local function may_inline_pure_binop()
    -- may inline (pure expression)
    local x = 10 + 20
    return x
end

local function may_inline_tuple()
    -- may inline if tuple semantics are correct
    local t = { a = 1, b = 2 }
    local iter, state, init = pairs(t)
    for k, v, n in iter, state, init do end -- n always nil in Luau
    return "done"
end

local function tuple_exact()
    local function returns_two()
        return "A", "B"
    end

    local a, b = returns_two()
    return a, b
end

local function tuple_less_than()
    local function returns_one()
        return "A"
    end

    local a, b = returns_one()
    return a, b
end

local function tuple_more_than()
    local function returns_three()
        return "A", "B", "C"
    end

    local a, b = returns_three()
    return a, b
end

local function tuple_unknown(flag)
    local function returns_unknown()
        if flag then
            return "A"
        end

        return "A", "B"
    end

    local a, b = returns_unknown()
    return a, b
end

local function may_inline_numeric_for()
    local start = 1
    local finish = 3
    local step = 1
    local sum = 0
    for i = start, finish, step do
        sum += i
    end
    return sum
end

local function may_inline_ipairs()
    local values = { "x", "y" }
    local iter, state, init = ipairs(values)
    local seen = ""
    for _, value in iter, state, init do
        seen ..= value
    end
    return seen
end

local function noinline_many_reads()
    -- must NOT inline; symbol is read multiple times
    local x = side_effect("E")
    return x, x
end

local function noinline_cond_jump()
    -- must NOT inline; symbol written inside loop branches (multiple writes)
    local x = 0
    for _ = 1, 3 do
        x = x + 1
    end
    return x
end

local function noinline_tuple_assign()
    -- must preserve left-to-right side-effect order
    local a, b = side_effect("F"), side_effect("G")
    return a, b
end

local function noinline_loop_condition()
    local counter = 0
    local function side_effect()
        counter += 1
        return true
    end

    local i = 0
    local x = side_effect()
    while x and i < 3 do
        i += 1
    end

    return counter
end

print(noinline_eval_order())
print(noinline_duplicate_exec())
print(noinline_nested_call())
print(may_inline())
print(may_inline_pure_binop())
print(may_inline_tuple())
print(select("#", tuple_exact()), tuple_exact())
print(select("#", tuple_less_than()), tuple_less_than())
print(select("#", tuple_more_than()), tuple_more_than())
print(select("#", tuple_unknown(true)), tuple_unknown(true))
print(may_inline_numeric_for())
print(may_inline_ipairs())
print(noinline_many_reads())
print(noinline_cond_jump())
print(noinline_tuple_assign())
print(noinline_loop_condition())
