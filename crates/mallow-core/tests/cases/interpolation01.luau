local function pair()
    return "first", "second"
end

local x = tonumber("5")
local name = tostring("mallow")

print(`{123} {newproxy() ~= nil}`)
print(`a{x}b{x + 1}c`)
print(`hello, {name}!`)
print(`{x}{x}`)
print(`100% of {name}`)
print(`literal %* and %%* stay text: {x}`)
print(`braces \{ } and backticks \` and "quotes": {x}`)
print(`{({ 1, 2, 3 })[2]} {#{ 4, 5 }}`)
print(`truncated: {pair()}`)
print(`nested: {`inner {x}`}`)
print(`héllo {name} 你好`)
print(`line\nbreak {x}\ttab`)
print(`{ {x} == {x} } and { ({x})[1] }`)
print(`{if x > 3 then "big" else "small"}`)

print(("%d items"):format(x))
print(("%* and %*"):format(pair()))
print(("%*"):format(x, "extra"))
