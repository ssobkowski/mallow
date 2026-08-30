local function triplet()
    return 10, 20, 30
end

local t = {}
t[5], t[6] = triplet()
print(t[1], t[2], t[3])
print(t[5], t[6], t[7])

local u = {1, 2, 3, 4}
u[5], u[6] = triplet()
print(u[1], u[4], u[5], u[6], u[7])
