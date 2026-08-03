local function add(use_vectors)
    local add_lhs = 1
    local add_rhs = 2
    if use_vectors then
        add_lhs = vector.create(1, 2, 3)
        add_rhs = vector.create(4, 5, 6)
    end
    return add_lhs + add_rhs
end

local function subtract(use_vectors)
    local subtract_lhs = 1
    local subtract_rhs = 2
    if use_vectors then
        subtract_lhs = vector.create(1, 2, 3)
        subtract_rhs = vector.create(4, 5, 6)
    end
    return subtract_lhs - subtract_rhs
end

print(add(true), subtract(false))
