local lume = (function()
    --
    -- lume
    --
    -- Copyright (c) 2020 rxi
    --
    -- Permission is hereby granted, free of charge, to any person obtaining a copy of
    -- this software and associated documentation files (the "Software"), to deal in
    -- the Software without restriction, including without limitation the rights to
    -- use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
    -- of the Software, and to permit persons to whom the Software is furnished to do
    -- so, subject to the following conditions:
    --
    -- The above copyright notice and this permission notice shall be included in all
    -- copies or substantial portions of the Software.
    --
    -- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    -- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
    -- FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    -- AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    -- LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    -- OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    -- SOFTWARE.
    --

    local lume = { _version = "2.3.0" }

    local pairs, ipairs = pairs, ipairs
    local type, assert, unpack = type, assert, unpack or table.unpack
    local tostring, tonumber = tostring, tonumber
    local math_floor = math.floor
    local math_ceil = math.ceil
    local math_atan2 = math.atan2 or math.atan
    local math_sqrt = math.sqrt
    local math_abs = math.abs

    local noop = function()
    end

    local identity = function(x)
      return x
    end

    local patternescape = function(str)
      return str:gsub("[%(%)%.%%%+%-%*%?%[%]%^%$]", "%%%1")
    end

    local absindex = function(len, i)
      return i < 0 and (len + i + 1) or i
    end

    local iscallable = function(x)
      if type(x) == "function" then return true end
      local mt = getmetatable(x)
      return mt and mt.__call ~= nil
    end

    local getiter = function(x)
      if lume.isarray(x) then
        return ipairs
      elseif type(x) == "table" then
        return pairs
      end
      error("expected table", 3)
    end

    local iteratee = function(x)
      if x == nil then return identity end
      if iscallable(x) then return x end
      if type(x) == "table" then
        return function(z)
          for k, v in pairs(x) do
            if z[k] ~= v then return false end
          end
          return true
        end
      end
      return function(z) return z[x] end
    end



    function lume.clamp(x, min, max)
      return x < min and min or (x > max and max or x)
    end


    function lume.round(x, increment)
      if increment then return lume.round(x / increment) * increment end
      return x >= 0 and math_floor(x + .5) or math_ceil(x - .5)
    end


    function lume.sign(x)
      return x < 0 and -1 or 1
    end


    function lume.lerp(a, b, amount)
      return a + (b - a) * lume.clamp(amount, 0, 1)
    end


    function lume.smooth(a, b, amount)
      local t = lume.clamp(amount, 0, 1)
      local m = t * t * (3 - 2 * t)
      return a + (b - a) * m
    end


    function lume.pingpong(x)
      return 1 - math_abs(1 - x % 2)
    end


    function lume.distance(x1, y1, x2, y2, squared)
      local dx = x1 - x2
      local dy = y1 - y2
      local s = dx * dx + dy * dy
      return squared and s or math_sqrt(s)
    end


    function lume.angle(x1, y1, x2, y2)
      return math_atan2(y2 - y1, x2 - x1)
    end


    function lume.vector(angle, magnitude)
      return math.cos(angle) * magnitude, math.sin(angle) * magnitude
    end


    function lume.random(a, b)
      if not a then a, b = 0, 1 end
      if not b then b = 0 end
      return a + math.random() * (b - a)
    end


    function lume.randomchoice(t)
      return t[math.random(#t)]
    end


    function lume.weightedchoice(t)
      local sum = 0
      for _, v in pairs(t) do
        assert(v >= 0, "weight value less than zero")
        sum = sum + v
      end
      assert(sum ~= 0, "all weights are zero")
      local rnd = lume.random(sum)
      for k, v in pairs(t) do
        if rnd < v then return k end
        rnd = rnd - v
      end
    end


    function lume.isarray(x)
      return type(x) == "table" and x[1] ~= nil
    end


    function lume.push(t, ...)
      local n = select("#", ...)
      for i = 1, n do
        t[#t + 1] = select(i, ...)
      end
      return ...
    end


    function lume.remove(t, x)
      local iter = getiter(t)
      for i, v in iter(t) do
        if v == x then
          if lume.isarray(t) then
            table.remove(t, i)
            break
          else
            t[i] = nil
            break
          end
        end
      end
      return x
    end


    function lume.clear(t)
      local iter = getiter(t)
      for k in iter(t) do
        t[k] = nil
      end
      return t
    end


    function lume.extend(t, ...)
      for i = 1, select("#", ...) do
        local x = select(i, ...)
        if x then
          for k, v in pairs(x) do
            t[k] = v
          end
        end
      end
      return t
    end


    function lume.shuffle(t)
      local rtn = {}
      for i = 1, #t do
        local r = math.random(i)
        if r ~= i then
          rtn[i] = rtn[r]
        end
        rtn[r] = t[i]
      end
      return rtn
    end


    function lume.sort(t, comp)
      local rtn = lume.clone(t)
      if comp then
        if type(comp) == "string" then
          table.sort(rtn, function(a, b) return a[comp] < b[comp] end)
        else
          table.sort(rtn, comp)
        end
      else
        table.sort(rtn)
      end
      return rtn
    end


    function lume.array(...)
      local t = {}
      for x in ... do t[#t + 1] = x end
      return t
    end


    function lume.each(t, fn, ...)
      local iter = getiter(t)
      if type(fn) == "string" then
        for _, v in iter(t) do v[fn](v, ...) end
      else
        for _, v in iter(t) do fn(v, ...) end
      end
      return t
    end


    function lume.map(t, fn)
      fn = iteratee(fn)
      local iter = getiter(t)
      local rtn = {}
      for k, v in iter(t) do rtn[k] = fn(v) end
      return rtn
    end


    function lume.all(t, fn)
      fn = iteratee(fn)
      local iter = getiter(t)
      for _, v in iter(t) do
        if not fn(v) then return false end
      end
      return true
    end


    function lume.any(t, fn)
      fn = iteratee(fn)
      local iter = getiter(t)
      for _, v in iter(t) do
        if fn(v) then return true end
      end
      return false
    end


    function lume.reduce(t, fn, first)
      local started = first ~= nil
      local acc = first
      local iter = getiter(t)
      for _, v in iter(t) do
        if started then
          acc = fn(acc, v)
        else
          acc = v
          started = true
        end
      end
      assert(started, "reduce of an empty table with no first value")
      return acc
    end


    function lume.unique(t)
      local rtn = {}
      for k in pairs(lume.invert(t)) do
        rtn[#rtn + 1] = k
      end
      return rtn
    end


    function lume.filter(t, fn, retainkeys)
      fn = iteratee(fn)
      local iter = getiter(t)
      local rtn = {}
      if retainkeys then
        for k, v in iter(t) do
          if fn(v) then rtn[k] = v end
        end
      else
        for _, v in iter(t) do
          if fn(v) then rtn[#rtn + 1] = v end
        end
      end
      return rtn
    end


    function lume.reject(t, fn, retainkeys)
      fn = iteratee(fn)
      local iter = getiter(t)
      local rtn = {}
      if retainkeys then
        for k, v in iter(t) do
          if not fn(v) then rtn[k] = v end
        end
      else
        for _, v in iter(t) do
          if not fn(v) then rtn[#rtn + 1] = v end
        end
      end
      return rtn
    end


    function lume.merge(...)
      local rtn = {}
      for i = 1, select("#", ...) do
        local t = select(i, ...)
        local iter = getiter(t)
        for k, v in iter(t) do
          rtn[k] = v
        end
      end
      return rtn
    end


    function lume.concat(...)
      local rtn = {}
      for i = 1, select("#", ...) do
        local t = select(i, ...)
        if t ~= nil then
          local iter = getiter(t)
          for _, v in iter(t) do
            rtn[#rtn + 1] = v
          end
        end
      end
      return rtn
    end


    function lume.find(t, value)
      local iter = getiter(t)
      for k, v in iter(t) do
        if v == value then return k end
      end
      return nil
    end


    function lume.match(t, fn)
      fn = iteratee(fn)
      local iter = getiter(t)
      for k, v in iter(t) do
        if fn(v) then return v, k end
      end
      return nil
    end


    function lume.count(t, fn)
      local count = 0
      local iter = getiter(t)
      if fn then
        fn = iteratee(fn)
        for _, v in iter(t) do
          if fn(v) then count = count + 1 end
        end
      else
        if lume.isarray(t) then
          return #t
        end
        for _ in iter(t) do count = count + 1 end
      end
      return count
    end


    function lume.slice(t, i, j)
      i = i and absindex(#t, i) or 1
      j = j and absindex(#t, j) or #t
      local rtn = {}
      for x = i < 1 and 1 or i, j > #t and #t or j do
        rtn[#rtn + 1] = t[x]
      end
      return rtn
    end


    function lume.first(t, n)
      if not n then return t[1] end
      return lume.slice(t, 1, n)
    end


    function lume.last(t, n)
      if not n then return t[#t] end
      return lume.slice(t, -n, -1)
    end


    function lume.invert(t)
      local rtn = {}
      for k, v in pairs(t) do rtn[v] = k end
      return rtn
    end


    function lume.pick(t, ...)
      local rtn = {}
      for i = 1, select("#", ...) do
        local k = select(i, ...)
        rtn[k] = t[k]
      end
      return rtn
    end


    function lume.keys(t)
      local rtn = {}
      local iter = getiter(t)
      for k in iter(t) do rtn[#rtn + 1] = k end
      return rtn
    end


    function lume.clone(t)
      local rtn = {}
      for k, v in pairs(t) do rtn[k] = v end
      return rtn
    end


    function lume.fn(fn, ...)
      assert(iscallable(fn), "expected a function as the first argument")
      local args = { ... }
      return function(...)
        local a = lume.concat(args, { ... })
        return fn(unpack(a))
      end
    end


    function lume.once(fn, ...)
      local f = lume.fn(fn, ...)
      local done = false
      return function(...)
        if done then return end
        done = true
        return f(...)
      end
    end


    local memoize_fnkey = {}
    local memoize_nil = {}

    function lume.memoize(fn)
      local cache = {}
      return function(...)
        local c = cache
        for i = 1, select("#", ...) do
          local a = select(i, ...) or memoize_nil
          c[a] = c[a] or {}
          c = c[a]
        end
        c[memoize_fnkey] = c[memoize_fnkey] or {fn(...)}
        return unpack(c[memoize_fnkey])
      end
    end


    function lume.combine(...)
      local n = select('#', ...)
      if n == 0 then return noop end
      if n == 1 then
        local fn = select(1, ...)
        if not fn then return noop end
        assert(iscallable(fn), "expected a function or nil")
        return fn
      end
      local funcs = {}
      for i = 1, n do
        local fn = select(i, ...)
        if fn ~= nil then
          assert(iscallable(fn), "expected a function or nil")
          funcs[#funcs + 1] = fn
        end
      end
      return function(...)
        for _, f in ipairs(funcs) do f(...) end
      end
    end


    function lume.call(fn, ...)
      if fn then
        return fn(...)
      end
    end


    function lume.time(fn, ...)
      local start = os.clock()
      local rtn = {fn(...)}
      return (os.clock() - start), unpack(rtn)
    end


    local lambda_cache = {}

    function lume.lambda(str)
      if not lambda_cache[str] then
        local args, body = str:match([[^([%w,_ ]-)%->(.-)$]])
        assert(args and body, "bad string lambda")
        local s = "return function(" .. args .. ")\nreturn " .. body .. "\nend"
        lambda_cache[str] = lume.dostring(s)
      end
      return lambda_cache[str]
    end


    local serialize

    local serialize_map = {
      [ "boolean" ] = tostring,
      [ "nil"     ] = tostring,
      [ "string"  ] = function(v) return string.format("%q", v) end,
      [ "number"  ] = function(v)
        if      v ~=  v     then return  "0/0"      --  nan
        elseif  v ==  1 / 0 then return  "1/0"      --  inf
        elseif  v == -1 / 0 then return "-1/0" end  -- -inf
        return tostring(v)
      end,
      [ "table"   ] = function(t, stk)
        stk = stk or {}
        if stk[t] then error("circular reference") end
        local rtn = {}
        stk[t] = true
        for k, v in pairs(t) do
          rtn[#rtn + 1] = "[" .. serialize(k, stk) .. "]=" .. serialize(v, stk)
        end
        stk[t] = nil
        return "{" .. table.concat(rtn, ",") .. "}"
      end
    }

    setmetatable(serialize_map, {
      __index = function(_, k) error("unsupported serialize type: " .. k) end
    })

    serialize = function(x, stk)
      return serialize_map[type(x)](x, stk)
    end

    function lume.serialize(x)
      return serialize(x)
    end


    function lume.deserialize(str)
      return lume.dostring("return " .. str)
    end


    function lume.split(str, sep)
      if not sep then
        return lume.array(str:gmatch("([%S]+)"))
      else
        assert(sep ~= "", "empty separator")
        local psep = patternescape(sep)
        return lume.array((str..sep):gmatch("(.-)("..psep..")"))
      end
    end


    function lume.trim(str, chars)
      if not chars then return str:match("^[%s]*(.-)[%s]*$") end
      chars = patternescape(chars)
      return str:match("^[" .. chars .. "]*(.-)[" .. chars .. "]*$")
    end


    function lume.wordwrap(str, limit)
      limit = limit or 72
      local check
      if type(limit) == "number" then
        check = function(s) return #s >= limit end
      else
        check = limit
      end
      local rtn = {}
      local line = ""
      for word, spaces in str:gmatch("(%S+)(%s*)") do
        local s = line .. word
        if check(s) then
          table.insert(rtn, line .. "\n")
          line = word
        else
          line = s
        end
        for c in spaces:gmatch(".") do
          if c == "\n" then
            table.insert(rtn, line .. "\n")
            line = ""
          else
            line = line .. c
          end
        end
      end
      table.insert(rtn, line)
      return table.concat(rtn)
    end


    function lume.format(str, vars)
      if not vars then return str end
      local f = function(x)
        return tostring(vars[x] or vars[tonumber(x)] or "{" .. x .. "}")
      end
      return (str:gsub("{(.-)}", f))
    end


    function lume.trace(...)
      local info = debug.getinfo(2, "Sl")
      local t = { info.short_src .. ":" .. info.currentline .. ":" }
      for i = 1, select("#", ...) do
        local x = select(i, ...)
        if type(x) == "number" then
          x = string.format("%g", lume.round(x, .01))
        end
        t[#t + 1] = tostring(x)
      end
      print(table.concat(t, " "))
    end


    function lume.dostring(str)
      return assert((loadstring or load)(str))()
    end


    function lume.uuid()
      local fn = function(x)
        local r = math.random(16) - 1
        r = (x == "x") and (r + 1) or (r % 4) + 9
        return ("0123456789abcdef"):sub(r, r)
      end
      return (("xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx"):gsub("[xy]", fn))
    end


    function lume.hotswap(modname)
      local oldglobal = lume.clone(_G)
      local updated = {}
      local function update(old, new)
        if updated[old] then return end
        updated[old] = true
        local oldmt, newmt = getmetatable(old), getmetatable(new)
        if oldmt and newmt then update(oldmt, newmt) end
        for k, v in pairs(new) do
          if type(v) == "table" then update(old[k], v) else old[k] = v end
        end
      end
      local err = nil
      local function onerror(e)
        for k in pairs(_G) do _G[k] = oldglobal[k] end
        err = lume.trim(e)
      end
      local ok, oldmod = pcall(require, modname)
      oldmod = ok and oldmod or nil
      xpcall(function()
        package.loaded[modname] = nil
        local newmod = require(modname)
        if type(oldmod) == "table" then update(oldmod, newmod) end
        for k, v in pairs(oldglobal) do
          if v ~= _G[k] and type(v) == "table" then
            update(v, _G[k])
            _G[k] = v
          end
        end
      end, onerror)
      package.loaded[modname] = oldmod
      if err then return nil, err end
      return oldmod
    end


    local ripairs_iter = function(t, i)
      i = i - 1
      local v = t[i]
      if v ~= nil then
        return i, v
      end
    end

    function lume.ripairs(t)
      return ripairs_iter, t, (#t + 1)
    end


    function lume.color(str, mul)
      mul = mul or 1
      local r, g, b, a
      r, g, b = str:match("#(%x%x)(%x%x)(%x%x)")
      if r then
        r = tonumber(r, 16) / 0xff
        g = tonumber(g, 16) / 0xff
        b = tonumber(b, 16) / 0xff
        a = 1
      elseif str:match("rgba?%s*%([%d%s%.,]+%)") then
        local f = str:gmatch("[%d.]+")
        r = (f() or 0) / 0xff
        g = (f() or 0) / 0xff
        b = (f() or 0) / 0xff
        a = f() or 1
      else
        error(("bad color string '%s'"):format(str))
      end
      return r * mul, g * mul, b * mul, a * mul
    end


    local chain_mt = {}
    chain_mt.__index = lume.map(lume.filter(lume, iscallable, true),
      function(fn)
        return function(self, ...)
          self._value = fn(self._value, ...)
          return self
        end
      end)
    chain_mt.__index.result = function(x) return x._value end

    function lume.chain(value)
      return setmetatable({ _value = value }, chain_mt)
    end

    setmetatable(lume,  {
      __call = function(_, ...)
        return lume.chain(...)
      end
    })


    return lume
end)()

-- Compares Lume values without depending on map key order.
local function same(actual, expected, seen)
    if actual == expected then
        return true
    end

    if actual ~= actual and expected ~= expected then
        return true
    end

    if type(actual) ~= "table" or type(expected) ~= "table" then
        return false
    end

    seen = seen or {}
    if seen[actual] == expected then
        return true
    end
    seen[actual] = expected

    for key, value in pairs(actual) do
        if not same(value, expected[key], seen) then
            return false
        end
    end

    for key, value in pairs(expected) do
        if not same(actual[key], value, seen) then
            return false
        end
    end

    return true
end

-- Runs one named Lume assertion group.
local function check(name, test)
    local ok, err = pcall(test)
    assert(ok, name .. ": " .. tostring(err))
end

-- Checks that a Lume operation raises an error.
local function rejects(name, operation)
    check(name, function()
        local ok = pcall(operation)
        assert(not ok, "operation unexpectedly succeeded")
    end)
end

-- Tests numeric helpers and interpolation.
check("numeric helpers", function()
    assert(lume.clamp(8, 5, 10) == 8)
    assert(lume.clamp(12, 5, 10) == 10)
    assert(lume.clamp(-1, 5, 10) == 5)
    assert(lume.round(0.5) == 1)
    assert(lume.round(-0.5) == -1)
    assert(lume.round(123, 10) == 120)
    assert(lume.round(-123.45, 0.1) == -123.5)
    assert(lume.sign(-10) == -1)
    assert(lume.sign(0) == 1)
    assert(lume.lerp(100, 200, 0.5) == 150)
    assert(lume.lerp(100, 200, 2) == 200)
    assert(lume.smooth(100, 200, 0.5) == 150)
    assert(lume.pingpong(1.5) == 0.5)
    assert(math.abs(lume.pingpong(-0.2) - 0.2) < 1e-9)
    assert(math.abs(lume.distance(13, 44, 156, 232) - 236.205419074) < 1e-9)

    local squared = lume.distance(13, 15, -2, 81, true)
    assert(squared == lume.distance(13, 15, -2, 81) ^ 2)
    assert(lume.angle(10, 10, 20, 20) == math.rad(45))

    local x, y = lume.vector(math.pi * 0.25, 100)
    assert(math.abs(x - 70.71067811865476) < 1e-6)
    assert(math.abs(y - 70.71067811865476) < 1e-6)
end)

-- Tests random helpers by checking their contracts instead of random values.
check("random helpers", function()
    math.randomseed(12345)

    assert(type(lume.random()) == "number")
    assert(type(lume.random(1)) == "number")
    assert(type(lume.random(1, 2)) == "number")
    assert(lume.randomchoice({ true }) == true)
    assert(lume.weightedchoice({ a = 1 }) == "a")
    assert(lume.weightedchoice({ a = 0, b = 1 }) == "b")

    local shuffled = lume.shuffle({ 1, 2, 3, 4, 5 })
    table.sort(shuffled)
    assert(same(shuffled, { 1, 2, 3, 4, 5 }))
    rejects("empty weighted choice", function() lume.weightedchoice({}) end)
    rejects("zero weighted choice", function() lume.weightedchoice({ a = 0, b = 0 }) end)
    rejects("negative weighted choice", function() lume.weightedchoice({ a = 1, b = -1 }) end)
end)

-- Tests mutation and table extension helpers.
check("table mutation", function()
    local values = { 1, 2 }
    local first, second = lume.push(values, 3, 4)
    assert(first == 3 and second == 4)
    lume.push(values, 5, nil, 6, nil, 7)
    assert(same(values, { 1, 2, 3, 4, 5, 6, 7 }))

    lume.remove(values, 3)
    assert(same(values, { 1, 2, 4, 5, 6, 7 }))
    lume.clear(values)
    assert(same(values, {}))

    local map = { a = 1, b = 2 }
    assert(lume.clear(map) == map)
    assert(same(map, {}))

    local extended = { a = 10, b = 20 }
    assert(lume.extend(extended) == extended)
    lume.extend(extended, { c = 30 }, { d = 40 })
    assert(same(extended, { a = 10, b = 20, c = 30, d = 40 }))
    lume.extend(extended, { a = "cat", b = "dog" }, { b = "owl" })
    assert(same(extended, { a = "cat", b = "owl", c = 30, d = 40 }))
end)

-- Tests iterator, mapping, and reduction helpers.
check("iterators and mapping", function()
    local array = lume.array(ipairs({ 0, 0, 0 }))
    assert(same(array, { 1, 2, 3 }))

    local keys = lume.array(pairs({ a = 0, b = 0, c = 0 }))
    table.sort(keys)
    assert(same(keys, { "a", "b", "c" }))

    local total = 1
    lume.each({ 1, 2, 3 }, function(value) total += value end)
    assert(total == 7)

    local method_total = 1
    local add = function(_, value) method_total += value end
    lume.each({ a = { add = add }, b = { add = add }, c = { add = function() end } }, "add", 10)
    assert(method_total == 21)

    assert(same(lume.map({ 1, 2, 3 }, function(value) return value * 2 end), { 2, 4, 6 }))
    assert(same(lume.map({ a = 2, b = 3 }, function(value) return value * 2 end), { a = 4, b = 6 }))
    assert(same(lume.map({ { id = 10 }, { id = 20 } }, "id"), { 10, 20 }))
    assert(same(lume.filter({ 1, 2, 3, 4, 5 }, function(value) return value % 2 == 0 end), { 2, 4 }))
    assert(same(lume.reject({ 1, 2, 3, 4, 5 }, function(value) return value % 2 == 0 end), { 1, 3, 5 }))
    assert(lume.all({ 2, 4, 6 }, function(value) return value % 2 == 0 end))
    assert(not lume.all({ 2, 3, 6 }, function(value) return value % 2 == 0 end))
    assert(lume.any({ 1, 3, 4 }, function(value) return value % 2 == 0 end))
    assert(not lume.any({ 1, 3, 5 }, function(value) return value % 2 == 0 end))

    assert(lume.reduce({ 1, 2, 3, 4 }, function(a, b) return a + b end) == 10)
    assert(lume.reduce({ 1, 2, 3, 4 }, function(a, b) return a + b end, 5) == 15)
    assert(lume.reduce({ false, true }, function(a, b) return a or b end) == true)
    rejects("reduce empty array", function() lume.reduce({}, function(a, b) return a + b end) end)
end)

-- Tests searching and collection transformations.
check("collection helpers", function()
    local unique_numbers = lume.unique({ 1, 2, 3, 2, 5, 6, 6 })
    table.sort(unique_numbers)
    assert(same(unique_numbers, { 1, 2, 3, 5, 6 }))

    local unique_words = lume.unique({ "a", "b", "c", "b", "d" })
    table.sort(unique_words)
    assert(same(unique_words, { "a", "b", "c", "d" }))

    assert(same(lume.merge({ a = 1, b = 2 }, { b = 3, c = 4 }), { a = 1, b = 3, c = 4 }))
    assert(same(lume.concat({ 1, 2 }, { 3, 4 }, nil, { 5 }), { 1, 2, 3, 4, 5 }))
    assert(lume.find({ "a", "b", "c" }, "b") == 2)
    assert(lume.find({ a = 1, b = 5, c = 7 }, 5) == "b")

    local value, index = lume.match({ "a", "b", "c", "d" }, function(item) return item > "c" end)
    assert(value == "d" and index == 4)
    assert(lume.count({ a = 1, b = 2, c = 5, [13] = 22, z = 8 }) == 5)
    assert(lume.count({ 5, 6, 7, 8 }, function(item) return item % 2 == 0 end) == 2)

    assert(same(lume.slice({ "a", "b", "c", "d", "e" }, 2, -2), { "b", "c", "d" }))
    assert(same(lume.first({ "a", "b", "c" }, 2), { "a", "b" }))
    assert(same(lume.last({ "a", "b", "c" }, 2), { "b", "c" }))

    local keys = lume.keys({ aaa = 1, bbb = 2, ccc = 3 })
    table.sort(keys)
    assert(same(keys, { "aaa", "bbb", "ccc" }))
    assert(same(lume.pick({ cat = 10, dog = 20, fox = 30 }, "cat", "fox"), { cat = 10, fox = 30 }))
    assert(same(lume.clone({ x = 2, y = "a" }), { x = 2, y = "a" }))
end)

-- Tests function combinators, memoization, and chaining.
check("function helpers", function()
    local bound = lume.fn(function(a, b) return a + b end, 10)
    assert(bound(5) == 15)
    rejects("invalid function binding", function() lume.fn(123) end)

    local once_calls = 0
    local once = lume.once(function(value) once_calls += value end)
    once(3)
    once(3)
    assert(once_calls == 3)

    local calls = 0
    local memoized = lume.memoize(function(a, b)
        calls += 1
        return a .. tostring(b)
    end)
    assert(memoized("hello", nil) == "hellonil")
    assert(memoized("hello", nil) == "hellonil")
    assert(calls == 1)

    local total = 0
    local combined = lume.combine(
        function(x, y) total += x + y end,
        function(x, y) total += x * y end
    )
    combined(10, 20)
    assert(total == 230)
    assert(lume.call(function(a, b) return a + b end, 1, 2) == 3)
    assert(lume.call(nil, 1, 2) == nil)

    local elapsed, a, b, c = lume.time(function(value) return 50, 60, value end, 70)
    assert(type(elapsed) == "number")
    assert(a == 50 and b == 60 and c == 70)

    assert(lume.chain({ 1, 2 }):map(function(value) return value * 2 end):result()[2] == 4)
    assert(lume(10):result() == 10)
end)

-- Tests serialization and the small expression language.
check("serialization and lambda", function()
    local value = { 1, 2, 3, true, false, "cat", { 4, 5 } }
    assert(same(lume.deserialize(lume.serialize(value)), value))
    assert(lume.deserialize(lume.serialize(math.huge)) == math.huge)
    assert(lume.deserialize(lume.serialize(-math.huge)) == -math.huge)
    local nan = lume.deserialize(lume.serialize(0 / 0))
    assert(nan ~= nan)

    assert(lume.lambda("x->x*x")(10) == 100)
    assert(lume.lambda("x,y -> 2*x+y")(10, 5) == 25)
    assert(lume.lambda("a -> 'hi->' .. a")("doggy") == "hi->doggy")
    rejects("invalid lambda", function() lume.lambda("abc") end)
    rejects("empty lambda", function() lume.lambda("") end)
end)

-- Tests string formatting and color parsing.
check("string helpers", function()
    assert(same(lume.split("cat   dog  pig"), { "cat", "dog", "pig" }))
    assert(same(lume.split("cat,dog,,pig", ","), { "cat", "dog", "", "pig" }))
    assert(same(lume.split("1<>2<>3", "<>"), { "1", "2", "3" }))
    assert(lume.trim("   hello world   ") == "hello world")
    assert(lume.trim("-=-hello-world===", "-=") == "hello-world")

    local wrapped = lume.wordwrap("A small string with some words and then some more   words", 20)
    assert(wrapped == "A small string with \nsome words and then \nsome more   words")
    assert(lume.format("a {a} in a {b}", { a = "mouse", b = "house" }) == "a mouse in a house")
    assert(lume.format("{missing} {keys}", {}) == "{missing} {keys}")

    assert(same({ lume.color("#ff0000") }, { 1, 0, 0, 1 }))
    assert(same({ lume.color("rgba(255, 255, 255, .5)") }, { 1, 1, 1, 0.5 }))
    rejects("invalid color", function() lume.color("#xyzxyz") end)
    rejects("empty color", function() lume.color("rgba()") end)
end)

-- Tests diagnostics, reverse iteration, and the module error path.
check("diagnostics and edge cases", function()
    local values = { "a", "b", false, "c" }
    local reversed = {}
    for index, value in lume.ripairs(values) do
        table.insert(reversed, { index, value })
    end
    assert(same(reversed, { { 4, "c" }, { 3, false }, { 2, "b" }, { 1, "a" } }))
    rejects("invalid reverse iterator", function() lume.ripairs(nil) end)
end)

print("lume: ok")
