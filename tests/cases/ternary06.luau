local results = {}

local function record(label, value)
    results[label] = value
end

local function repr(value)
    if value == nil then return "nil" end
    if type(value) == "boolean" then return tostring(value) end
    if type(value) == "number" then return tostring(value) end
    if type(value) == "string" then return `"{value}"` end
    return tostring(value)
end

local function capture(label, value)
    record(label, repr(value))
end

local function capture_trace(label, trace)
    record(label, #trace == 0 and "(empty)" or table.concat(trace, ">"))
end

local function step(trace, tag, value)
    table.insert(trace, tag)
    return value
end

local values = {
    { name = "false", value = false },
    { name = "nil",   value = nil   },
    { name = "zero",  value = 0     },  -- 0 is TRUTHY in Lua; trips decompilers assuming C semantics
    { name = "str",   value = "STR" },
}

-- not-prefixed ternary

local function test_not_ternary(a, b, c, label)
    local value = not a and b or c
    capture(`not_ternary:{label}`, value)
end

local function test_not_ternary_trace(a, b, c, label)
    local trace = {}
    local value = not a and step(trace, "then", b) or step(trace, "else", c)
    capture(`not_ternary_trace:{label}:value`, value)
    capture_trace(`not_ternary_trace:{label}:trace`, trace)
end

-- cross product: a in {false, nil, 0, "STR"} x b,c in values
for _, b in values do
    for _, c in values do
        local bc = `{b.name}:{c.name}`
        test_not_ternary(false, b.value, c.value, `F:{bc}`)
        test_not_ternary(nil,   b.value, c.value, `N:{bc}`)
        test_not_ternary(0,     b.value, c.value, `Z:{bc}`)   -- not 0 = false -> always else
        test_not_ternary("X",   b.value, c.value, `S:{bc}`)   -- not "X" = false -> always else
    end
end

test_not_ternary_trace(false, "YES", "NO",   "F:str-str")
test_not_ternary_trace(nil,   "YES", "NO",   "N:str-str")
test_not_ternary_trace(0,     "YES", "NO",   "Z:str-str")
test_not_ternary_trace("X",   "YES", "NO",   "S:str-str")
test_not_ternary_trace(false, false, "NO",   "F:false-then")   -- then value is falsy: falls to else
test_not_ternary_trace(false, nil,   "NO",   "F:nil-then")     -- same
test_not_ternary_trace(false, false, false,  "F:false-both")
test_not_ternary_trace(false, nil,   nil,    "F:nil-both")

-- a and not b or c

local function test_and_not(a, b, c, label)
    local value = a and not b or c
    capture(`and_not:{label}`, value)
end

test_and_not(true,  false, "NO",  "T:F")
test_and_not(true,  true,  "NO",  "T:T")           -- "then" is false, falls to "NO"
test_and_not(true,  "X",   "NO",  "T:S")           -- "then" is false, falls to "NO"
test_and_not(true,  nil,   "NO",  "T:N")           -- "then" is true, result is true
test_and_not(false, false, "NO",  "F:F")
test_and_not(false, true,  "NO",  "F:T")
test_and_not(true,  false, false, "T:F:false-else")
test_and_not(true,  false, nil,   "T:F:nil-else")
test_and_not(true,  true,  false, "T:T:false-else") -- not b=false, falls to c=false
test_and_not(true,  true,  nil,   "T:T:nil-else")   -- not b=false, falls to c=nil

-- not (compound) and ternary

local function test_not_and_compound(a, b, c, d, label)
    local value = not (a and b) and c or d
    capture(`not_and_compound:{label}`, value)
end

local function test_not_or_compound(a, b, c, d, label)
    local value = not (a or b) and c or d
    capture(`not_or_compound:{label}`, value)
end

test_not_and_compound(true,  true,  "YES", "NO",  "tt")   -- not true -> "NO"
test_not_and_compound(true,  false, "YES", "NO",  "tf")   -- not false -> "YES"
test_not_and_compound(false, true,  "YES", "NO",  "ft")
test_not_and_compound(false, false, "YES", "NO",  "ff")
test_not_and_compound(true,  true,  false, "NO",  "tt:false-yes")
test_not_and_compound(true,  true,  nil,   "NO",  "tt:nil-yes")
test_not_and_compound(true,  false, false, "NO",  "tf:false-yes")  -- not false=true, c=false -> falls to d
test_not_and_compound(true,  false, nil,   "NO",  "tf:nil-yes")

test_not_or_compound(true,  true,  "YES", "NO",  "tt")   -- not true -> "NO"
test_not_or_compound(true,  false, "YES", "NO",  "tf")   -- not true -> "NO"
test_not_or_compound(false, false, "YES", "NO",  "ff")   -- not false -> "YES"
test_not_or_compound(false, false, false, "NO",  "ff:false-yes")
test_not_or_compound(false, false, nil,   "NO",  "ff:nil-yes")

-- double not (boolean normalization)

local function test_double_not(a, label)
    local value = not not a
    capture(`double_not:{label}`, value)
end

local function test_double_not_ternary(a, yes, no, label)
    local value = not not a and yes or no
    capture(`double_not_ternary:{label}`, value)
end

for _, v in values do
    test_double_not(v.value, v.name)
end
test_double_not(1,   "one")
test_double_not("",  "empty-str")
test_double_not(0.0, "zero-float")

test_double_not_ternary(false, "YES", "NO",  "false")
test_double_not_ternary(nil,   "YES", "NO",  "nil")
test_double_not_ternary(0,     "YES", "NO",  "zero")
test_double_not_ternary("X",   "YES", "NO",  "str")
test_double_not_ternary(false, false, "NO",  "false:false-yes")
test_double_not_ternary(0,     false, "NO",  "zero:false-yes")  -- 0 truthy, not not 0 = true, c=false -> d

-- or-chain (4 operands)

local function test_or4(a, b, c, d, label)
    local value = a or b or c or d
    capture(`or4:{label}`, value)
end

local function test_or4_trace(a, b, c, d, label)
    local trace = {}
    local value = step(trace, "a", a) or step(trace, "b", b) or step(trace, "c", c) or step(trace, "d", d)
    capture(`or4_trace:{label}:value`, value)
    capture_trace(`or4_trace:{label}:trace`, trace)
end

test_or4(false, false, false, "D",    "fff-str")
test_or4(false, false, nil,   "D",    "ffn-str")
test_or4(false, nil,   false, false,  "fnff")   -- all falsy, returns false
test_or4(nil,   nil,   nil,   nil,    "nnnn")   -- all nil, returns nil
test_or4(false, false, false, false,  "ffff")   -- all false, returns false
test_or4("A",   false, false, "D",    "a-ffd")  -- short-circuits at "A"
test_or4(false, "B",   false, "D",    "f-b-fd")
test_or4(0,     false, nil,   "D",    "zero-fn-d")  -- 0 is truthy! short-circuits
test_or4(false, 0,     nil,   "D",    "f-zero-nd")
test_or4(nil,   false, 0,     nil,    "nf-zero-n")

test_or4_trace(false, false, false, "D",   "fff-str")
test_or4_trace(false, nil,   false, "D",   "fn-f-str")
test_or4_trace(false, false, "C",   "D",   "ff-c-str")
test_or4_trace("A",   false, false, "D",   "a-ffd")
test_or4_trace(false, false, nil,   nil,   "ffnn")
test_or4_trace(0,     false, nil,   "D",   "zero-fn-str") -- stops at 0

-- and-chain (4 operands)

local function test_and4(a, b, c, d, label)
    local value = a and b and c and d
    capture(`and4:{label}`, value)
end

local function test_and4_trace(a, b, c, d, label)
    local trace = {}
    local value = step(trace,"a",a) and step(trace,"b",b) and step(trace,"c",c) and step(trace,"d",d)
    capture(`and4_trace:{label}:value`, value)
    capture_trace(`and4_trace:{label}:trace`, trace)
end

test_and4("A", "B", "C", "D",    "all-str")
test_and4("A", "B", "C", false,  "last-false")
test_and4("A", "B", false, "D",  "third-false")
test_and4("A", false, "C", "D",  "second-false")
test_and4(false, "B", "C", "D",  "first-false")
test_and4("A", "B", "C", nil,    "last-nil")
test_and4(nil, "B", "C", "D",    "first-nil")
test_and4(0, "B", "C", "D",      "first-zero")
test_and4("A", 0, false, "D",    "z-then-false")
test_and4("A", "B", "C", 0,      "last-zero")
test_and4(false, nil, "C", "D",  "first-false-second-nil")

test_and4_trace("A", "B", "C", "D",   "all-str")
test_and4_trace("A", false, "C", "D", "second-false")
test_and4_trace(false, "B", "C", "D", "first-false")
test_and4_trace("A", "B", nil, "D",   "third-nil")
test_and4_trace(0, "B", "C", false,   "first-zero-last-false")

-- and-chain as ternary condition

local function test_and_cond(a, b, c, d, label)
    local value = a and b and c or d
    capture(`and_cond:{label}`, value)
end

local function test_and_cond_trace(a, b, c, d, label)
    local trace = {}
    local value = a and b and step(trace, "then", c) or step(trace, "else", d)
    capture(`and_cond_trace:{label}:value`, value)
    capture_trace(`and_cond_trace:{label}:trace`, trace)
end

test_and_cond("A", "B", "YES", "NO",   "tt-str")
test_and_cond("A", false, "YES", "NO", "tf")
test_and_cond(false, "B", "YES", "NO", "ft")
test_and_cond(false, false, "YES", "NO","ff")
test_and_cond("A", "B", false, "NO",   "tt-false-yes")  -- c=false -> falls to d
test_and_cond("A", "B", nil,   "NO",   "tt-nil-yes")    -- c=nil -> falls to d
test_and_cond("A", "B", "YES", false,  "tt-false-no")
test_and_cond("A", "B", false, false,  "tt-ff")         -- c=false->d=false -> false
test_and_cond("A", "B", nil,   nil,    "tt-nn")
test_and_cond(0,   "B", false, "NO",   "zero-B-false-yes") -- 0 truthy, c=false -> "NO"

test_and_cond_trace("A", "B", "YES", "NO",   "tt")
test_and_cond_trace("A", false, "YES", "NO", "tf")
test_and_cond_trace(false, "B", "YES", "NO", "ft")
test_and_cond_trace("A", "B", false, "NO",   "tt-false-yes")
test_and_cond_trace("A", "B", nil,   "NO",   "tt-nil-yes")
test_and_cond_trace(0, "B", false, "NO",     "zero-B-false-yes")

-- or-of-ands (precedence trap)

local function test_or_of_ands(a, b, c, d, label)
    local value = a and b or c and d
    capture(`or_of_ands:{label}`, value)
end

local function test_or_of_ands_trace(a, b, c, d, label)
    local trace = {}
    local function get_b() table.insert(trace, "b"); return b end
    local function get_d() table.insert(trace, "d"); return d end
    local value = a and get_b() or c and get_d()
    capture(`or_of_ands_trace:{label}:value`, value)
    capture_trace(`or_of_ands_trace:{label}:trace`, trace)
end

test_or_of_ands("A", "B",   "C", "D",   "tt-tt")
test_or_of_ands("A", false, "C", "D",   "tf-tt")  -- A and false=false -> C and D = D
test_or_of_ands("A", nil,   "C", "D",   "tn-tt")
test_or_of_ands(false, "B", "C", "D",   "ft-tt")  -- false->C and D=D
test_or_of_ands(false, "B", false, "D", "ft-ft")  -- false->false and D=false
test_or_of_ands(false, "B", "C", false, "ft-tf")
test_or_of_ands(false, "B", "C", nil,   "ft-tn")
test_or_of_ands("A",   false, false, "D", "tf-ft")
test_or_of_ands("A",   false, "C", false, "tf-tf")
test_or_of_ands("A",   false, false, false, "tf-ff")
test_or_of_ands(false, false, false, false, "ff-ff")
test_or_of_ands(false, "B", "C", 0,     "ft-t0")

test_or_of_ands_trace("A", "B",   "C", "D",   "tt-tt")
test_or_of_ands_trace("A", false, "C", "D",   "tf-tt")
test_or_of_ands_trace(false, "B", "C", "D",   "ft-tt")
test_or_of_ands_trace(false, "B", false, "D", "ft-ft")
test_or_of_ands_trace("A", "B",   false, "D", "tt-ft-nofallthrough") -- b truthy -> short-circuit, d never read

-- triple nesting

local function test_triple(a, b, c, d, e, f, g, label)
    local value = a and (b and (c and d or e) or f) or g
    capture(`triple:{label}`, value)
end

local function test_triple_trace(a, b, c, d, e, f, g, label)
    local trace = {}
    local value = a
        and (b
            and (c and step(trace,"dd",d) or step(trace,"ee",e))
            or step(trace,"ff",f))
        or step(trace,"gg",g)
    capture(`triple_trace:{label}:value`, value)
    capture_trace(`triple_trace:{label}:trace`, trace)
end

test_triple(true,  true,  true,  "D", "E", "F", "G", "ttt")
test_triple(true,  true,  false, "D", "E", "F", "G", "ttf:c-false")   -- c=false -> e
test_triple(true,  true,  nil,   "D", "E", "F", "G", "ttn:c-nil")
test_triple(true,  true,  true,  false, "E", "F", "G", "ttt:d-false") -- d=false -> e
test_triple(true,  true,  true,  nil,   "E", "F", "G", "ttt:d-nil")   -- d=nil -> e
test_triple(true,  false, "C",   "D",  "E", "F", "G", "tft")         -- b=false -> f
test_triple(true,  false, "C",   "D",  "E", nil,  "G", "tft:f-nil")  -- b=false -> f=nil -> g
test_triple(false, true,  true,  "D",  "E", "F",  "G", "ftt")        -- a=false -> g
test_triple(false, false, false, "D",  "E", "F",  "G", "fff")
test_triple(false, true,  true,  "D",  "E", "F",  false, "ftt:g-false")
test_triple(false, true,  true,  "D",  "E", "F",  nil,   "ftt:g-nil")
test_triple(true,  true,  true,  false, false, "F", "G", "ttt:d-false:e-false") -- d=false->e=false->falls to? NO: c and d or e = false and false or... wait
-- Let me trace: c=true, d=false -> (c and d) = false; false or e=false -> false; b and false or f = false or "F" = "F"; a and "F" or g = "F"
test_triple(true,  true,  true,  nil, nil, "F", "G", "ttt:d-nil:e-nil") -- same logic -> "F"

test_triple_trace(true,  true,  true,  "D", "E", "F", "G", "ttt")
test_triple_trace(true,  true,  false, "D", "E", "F", "G", "ttf")
test_triple_trace(true,  false, "C",   "D", "E", "F", "G", "tft")
test_triple_trace(false, true,  true,  "D", "E", "F", "G", "ftt")
test_triple_trace(true,  true,  true,  false, "E", "F", "G", "ttt:d-false")
test_triple_trace(true,  true,  true,  nil,   "E", "F", "G", "ttt:d-nil")
test_triple_trace(true,  false, "C",   "D",  "E", nil, "G", "tft:f-nil")

-- elseif-chain with not

local function test_elseif_not(a, b, c, d, e, label)
    local value = not a and b or not c and d or e
    capture(`elseif_not:{label}`, value)
end

local function test_elseif_not_trace(a, b, c, d, e, label)
    local trace = {}
    local value = not a and step(trace,"if",b) or not c and step(trace,"elseif",d) or step(trace,"else",e)
    capture(`elseif_not_trace:{label}:value`, value)
    capture_trace(`elseif_not_trace:{label}:trace`, trace)
end

test_elseif_not(false, "B", false, "D",  "E",   "fn-fn")
test_elseif_not(false, "B", true,  "D",  "E",   "fn-tn")
test_elseif_not(true,  "B", false, "D",  "E",   "tn-fn")
test_elseif_not(true,  "B", true,  "D",  "E",   "tn-tn")
test_elseif_not(false, false, false, "D", "E",  "if-false-b")     -- b=false -> falls to elseif
test_elseif_not(false, nil,   false, "D", "E",  "if-nil-b")       -- b=nil -> falls to elseif
test_elseif_not(true,  "B",  false, false, "E", "elseif-false-d") -- d=false -> falls to else
test_elseif_not(true,  "B",  false, nil,   "E", "elseif-nil-d")
test_elseif_not(true,  "B",  true,  "D",  false,"else-false-e")
test_elseif_not(true,  "B",  true,  "D",  nil,  "else-nil-e")
test_elseif_not(false, false, true, "D",  false,"if-false-b:else-false") -- b=false falls to elseif, but not c=false so falls to else=false

test_elseif_not_trace(false, "B",   false, "D", "E", "fn-fn")
test_elseif_not_trace(true,  "B",   false, "D", "E", "tn-fn")
test_elseif_not_trace(true,  "B",   true,  "D", "E", "tn-tn")
test_elseif_not_trace(false, false, false, "D", "E", "if-false-b")
test_elseif_not_trace(false, nil,   false, "D", "E", "if-nil-b")

-- comparison operators as conditions

local function test_cmp_ternary(a, b, yes, no, label)
    local value = (a > b) and yes or no
    capture(`cmp_ternary:{label}`, value)
end

local function test_neq_ternary(a, b, yes, no, label)
    local value = (a ~= b) and yes or no
    capture(`neq_ternary:{label}`, value)
end

local function test_multi_cmp(a, b, c, yes, no, label)
    local value = (a > b) and (b > c) and yes or no
    capture(`multi_cmp:{label}`, value)
end

test_cmp_ternary(5, 3, "YES", "NO",   "5>3")
test_cmp_ternary(3, 5, "YES", "NO",   "3<5")
test_cmp_ternary(3, 3, "YES", "NO",   "eq")
test_cmp_ternary(5, 3, false, "NO",   "5>3:false-yes")  -- yes=false -> falls to "NO"!
test_cmp_ternary(5, 3, nil,   "NO",   "5>3:nil-yes")
test_cmp_ternary(5, 3, "YES", false,  "5>3:false-no")
test_cmp_ternary(3, 5, "YES", false,  "3<5:false-no")
test_cmp_ternary(3, 5, "YES", nil,    "3<5:nil-no")

test_neq_ternary("A", "B", "YES", "NO",   "neq")
test_neq_ternary("A", "A", "YES", "NO",   "eq")
test_neq_ternary("A", "B", false, "NO",   "neq:false-yes")
test_neq_ternary("A", "A", "YES", false,  "eq:false-no")
test_neq_ternary("A", "B", nil,   "NO",   "neq:nil-yes")

test_multi_cmp(5, 3, 1, "YES", "NO",   "5>3>1")
test_multi_cmp(5, 3, 4, "YES", "NO",   "5>3,3<4")
test_multi_cmp(1, 3, 0, "YES", "NO",   "1<3")
test_multi_cmp(5, 3, 1, false, "NO",   "5>3>1:false-yes")
test_multi_cmp(5, 3, 1, nil,   "NO",   "5>3>1:nil-yes")
test_multi_cmp(5, 3, 4, false, "NO",   "5>3,3<4:false-yes") -- cond false anyway

-- De Morgan patterns

local function test_demorgan_nand(a, b, yes, no, label)
    local value = (not a or not b) and yes or no
    capture(`demorgan_nand:{label}`, value)
end

local function test_demorgan_nor(a, b, yes, no, label)
    local value = (not a and not b) and yes or no
    capture(`demorgan_nor:{label}`, value)
end

test_demorgan_nand(true,  true,  "YES", "NO",  "tt")  -- not a or not b = false -> "NO"
test_demorgan_nand(true,  false, "YES", "NO",  "tf")
test_demorgan_nand(false, true,  "YES", "NO",  "ft")
test_demorgan_nand(false, false, "YES", "NO",  "ff")
test_demorgan_nand(true,  true,  false, "NO",  "tt:false-yes")
test_demorgan_nand(false, false, false, "NO",  "ff:false-yes")  -- cond=true, c=false -> d
test_demorgan_nand(false, false, nil,   "NO",  "ff:nil-yes")

test_demorgan_nor(true,  true,  "YES", "NO",  "tt")   -- not a and not b = false -> "NO"
test_demorgan_nor(true,  false, "YES", "NO",  "tf")
test_demorgan_nor(false, false, "YES", "NO",  "ff")   -- both not -> true -> "YES"
test_demorgan_nor(false, false, false, "NO",  "ff:false-yes")
test_demorgan_nor(false, false, nil,   "NO",  "ff:nil-yes")

-- not and not

local function test_not_and_not(a, b, c, d, label)
    local value = not a and not b and c or d
    capture(`not_and_not:{label}`, value)
end

test_not_and_not(false, false, "YES", "NO",  "ff")
test_not_and_not(false, true,  "YES", "NO",  "ft")
test_not_and_not(true,  false, "YES", "NO",  "tf")
test_not_and_not(true,  true,  "YES", "NO",  "tt")
test_not_and_not(false, false, false, "NO",  "ff:false-yes")
test_not_and_not(false, false, nil,   "NO",  "ff:nil-yes")
test_not_and_not(false, false, "YES", false, "ff:false-no")
test_not_and_not(nil,   nil,   "YES", "NO",  "nn")  -- nil is falsy, not nil=true -> "YES"
test_not_and_not(0,     false, "YES", "NO",  "zero-f") -- not 0=false -> "NO"

-- self-referential  a and a or b

local function test_self_or(a, b, label)
    local value = a and a or b
    capture(`self_or:{label}`, value)
end

for _, v in values do
    test_self_or(v.value, "FALLBACK", v.name)
end
test_self_or(false, false, "false:false-fallback")
test_self_or(nil,   nil,   "nil:nil-fallback")
test_self_or(0,     false, "zero:false-fallback")  -- a=0 truthy -> returns 0

--  or-chain as ternary default

local function test_or_in_then(a, b, c, d, label)
    local value = a and (b or c) or d
    capture(`or_in_then:{label}`, value)
end

local function test_or_in_then_trace(a, b, c, d, label)
    local trace = {}
    local value = a and (step(trace,"b",b) or step(trace,"c",c)) or step(trace,"d",d)
    capture(`or_in_then_trace:{label}:value`, value)
    capture_trace(`or_in_then_trace:{label}:trace`, trace)
end

test_or_in_then(true,  "B", "C", "D",   "T:b-c-d")
test_or_in_then(true,  false, "C", "D", "T:false-C-d")
test_or_in_then(true,  nil,   "C", "D", "T:nil-C-d")
test_or_in_then(true,  false, false, "D","T:ff-d")   -- b or c = false, a and false -> d
test_or_in_then(true,  false, nil, "D",  "T:fn-d")   -- b or c = nil -> a and nil -> d
test_or_in_then(true,  nil,   nil, "D",  "T:nn-d")
test_or_in_then(false, "B",   "C", "D",  "F:b-c-d")
test_or_in_then(false, false, false, "D","F:ff-d")

test_or_in_then_trace(true,  "B",   "C", "D",  "T:b-str")
test_or_in_then_trace(true,  false, "C", "D",  "T:false-c")
test_or_in_then_trace(true,  false, nil, "D",  "T:fn-d")   -- b or c = nil -> falls to d
test_or_in_then_trace(false, "B",   "C", "D",  "F:b-str")

local keys = {}
for k, _ in results do
    table.insert(keys, k)
end
table.sort(keys)

for _, k in keys do
    print(`{k}={results[k]}`)
end

print(`TOTAL={#keys}`)
