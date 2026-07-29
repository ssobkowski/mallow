local memo = {}

local function lookup(n)
    local cached = memo[n]
    if cached then
        return cached
    end
    memo[n] = n
    return n
end

print(lookup(1), lookup(2))
