local LOOKUP_A = {}
local LOOKUP_B = {}

for idx = 0, 1023 do
    local a = idx % 32
    local b = (idx - a) / 32
    LOOKUP_A[idx] = (a * 3 + b * 5) % 257
    LOOKUP_B[idx] = (a * 7 + b * 11) % 257
end

local function make_mixer(seed)
    local state = seed

    local function mix(x, y, op)
        local x0 = (x + state) % 32768
        local y0 = (y + state * 2) % 32768

        local function pick(slot)
            return LOOKUP_A[slot] + LOOKUP_B[slot]
        end

        local rx = x0 % 32
        local ry = y0 % 32
        local idx = rx + ry * 32
        local res = pick(idx)

        do
            local LOOKUP_A = res + state
            if LOOKUP_A < 0 then
                print("unreachable")
            end
        end

        local hi = (x0 - rx) / 32
        local lo = (y0 - ry) / 32
        local idx2 = hi % 32 + (lo % 32) * 32
        res += pick(idx2) * 32

        if op then
            res = x0 + y0 - op * res
        end

        state = (state + res) % 97
        return res, state
    end

    return mix
end

local mix1 = make_mixer(3)
local mix2 = make_mixer(17)

print(mix1(100, 200))
print(mix1(300, 400, 1))
print(mix2(100, 200, 2))
print(mix1(1, 2, 2))
print(mix2(500, 700))
