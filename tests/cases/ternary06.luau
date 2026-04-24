local results = {}

local function record(label, value)
    results[label] = value
end

local function repr(value)
    if value == nil then
        return "nil"
    end

    if type(value) == "string" then
        return `"{value}"`
    end

    return `{value}`
end

local function capture(label, value)
    record(label, repr(value))
end

local function capture_trace(label, trace)
    record(label, table.concat(trace, ">"))
end

local function step(trace, tag, value)
    table.insert(trace, tag)
    return value
end

local values = {
    {name = "false", value = false},
    {name = "nil", value = nil},
    {name = "left", value = "LEFT"},
    {name = "zero", value = 0},
    {name = "right", value = "RIGHT"},
}

local function test_if_value(cond, yes, no, label)
    local value = cond and yes or no
    capture(`if_value:{label}`, value)
end

local function test_if_trace(cond, yes, no, label)
    local trace = {}
    local value = cond and step(trace, "then", yes) or step(trace, "else", no)
    capture(`if_trace:{label}:value`, value)
    capture_trace(`if_trace:{label}:trace`, trace)
end

local function test_nested_if(a, b, c, d, e, label)
    local value = a and (b and c or d) or e
    capture(`nested_if:{label}`, value)
end

local function test_nested_if_trace(a, b, c, d, e, label)
    local trace = {}
    local value = a and (b and step(trace, "then-then", c) or step(trace, "then-else", d)) or step(trace, "else", e)
    capture(`nested_trace:{label}:value`, value)
    capture_trace(`nested_trace:{label}:trace`, trace)
end

local function test_elseif_value(a, b, c, d, e, label)
    local value = a and c or b and d or e
    capture(`elseif:{label}`, value)
end

local function test_elseif_trace(a, b, c, d, e, label)
    local trace = {}
    local value = a and step(trace, "if", c) or b and step(trace, "elseif", d) or step(trace, "else", e)
    capture(`elseif_trace:{label}:value`, value)
    capture_trace(`elseif_trace:{label}:trace`, trace)
end

local function test_if_short_circuit(a, b, c, d, label)
    local value = a and (b and c) or (d or "FALLBACK")
    capture(`if_short:{label}`, value)
end

for _, yes in ipairs(values) do
    for _, no in ipairs(values) do
        local label = `{yes.name}:{no.name}`
        test_if_value(true, yes.value, no.value, `T:{label}`)
        test_if_value(false, yes.value, no.value, `F:{label}`)
    end
end

test_if_trace(true, false, "RIGHT", "true:false:right")
test_if_trace(true, nil, "RIGHT", "true:nil:right")
test_if_trace(true, "LEFT", "RIGHT", "true:left:right")
test_if_trace(false, "LEFT", false, "false:left:false")
test_if_trace(false, "LEFT", nil, "false:left:nil")
test_if_trace(false, false, "RIGHT", "false:false:right")

test_nested_if(true, true, false, "D", "E", "tt:false")
test_nested_if(true, true, nil, "D", "E", "tt:nil")
test_nested_if(true, true, "C", false, "E", "tt:string")
test_nested_if(true, false, "C", false, "E", "te:false")
test_nested_if(true, false, "C", nil, "E", "te:nil")
test_nested_if(false, true, "C", "D", false, "ef:false")
test_nested_if(false, false, "C", "D", nil, "ef:nil")
test_nested_if(false, true, "C", "D", "E", "ef:string")

test_nested_if_trace(true, true, false, "D", "E", "tt:false")
test_nested_if_trace(true, false, "C", nil, "E", "te:nil")
test_nested_if_trace(false, true, "C", "D", false, "ef:false")

test_elseif_value(true, true, false, "D", "E", "if:false")
test_elseif_value(true, false, nil, "D", "E", "if:nil")
test_elseif_value(false, true, "C", false, "E", "elseif:false")
test_elseif_value(false, true, "C", nil, "E", "elseif:nil")
test_elseif_value(false, false, "C", "D", false, "else:false")
test_elseif_value(false, false, "C", "D", nil, "else:nil")
test_elseif_value(false, false, "C", "D", "E", "else:string")

test_elseif_trace(true, true, false, "D", "E", "if:false")
test_elseif_trace(false, true, "C", nil, "E", "elseif:nil")
test_elseif_trace(false, false, "C", "D", false, "else:false")

test_if_short_circuit(true, true, false, "RIGHT", "then:false")
test_if_short_circuit(true, true, nil, "RIGHT", "then:nil")
test_if_short_circuit(true, false, "LEFT", "RIGHT", "then-guard-false")
test_if_short_circuit(false, true, "LEFT", false, "else:false")
test_if_short_circuit(false, true, "LEFT", nil, "else:nil")
test_if_short_circuit(false, true, "LEFT", "RIGHT", "else:string")

local keys = {}
for k, _ in results do
    table.insert(keys, k)
end
table.sort(keys)

for _, k in keys do
    print(`{k}={results[k]}`)
end

print(`TOTAL={#keys}`)
