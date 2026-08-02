local inspect = (function()
    local _tl_compat; if (tonumber((_VERSION or ''):match('[%d.]*$')) or 0) < 5.3 then local p, m = pcall(require, 'compat53.module'); if p then _tl_compat = m end end; local math = _tl_compat and _tl_compat.math or math; local pcall = _tl_compat and _tl_compat.pcall or pcall; local string = _tl_compat and _tl_compat.string or string; local table = _tl_compat and _tl_compat.table or table; local type = type
    local inspect = { Options = {} }

















    inspect._VERSION = 'inspect.lua 3.1.0'
    inspect._URL = 'http://github.com/kikito/inspect.lua'
    inspect._DESCRIPTION = 'human-readable representations of tables'
    inspect._LICENSE = [[
      MIT LICENSE

      Copyright (c) 2022 Enrique García Cota

      Permission is hereby granted, free of charge, to any person obtaining a
      copy of this software and associated documentation files (the
      "Software"), to deal in the Software without restriction, including
      without limitation the rights to use, copy, modify, merge, publish,
      distribute, sublicense, and/or sell copies of the Software, and to
      permit persons to whom the Software is furnished to do so, subject to
      the following conditions:

      The above copyright notice and this permission notice shall be included
      in all copies or substantial portions of the Software.

      THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
      OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
      MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
      IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
      CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
      TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
      SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
    ]]
    inspect.KEY = setmetatable({}, { __tostring = function() return 'inspect.KEY' end })
    inspect.METATABLE = setmetatable({}, { __tostring = function() return 'inspect.METATABLE' end })

    local tostring = tostring
    local rep = string.rep
    local match = string.match
    local char = string.char
    local gsub = string.gsub
    local fmt = string.format


    local sbavailable, stringbuffer = pcall(require, "string.buffer")
    local buffnew
    local puts
    local render

    if sbavailable then
       buffnew = stringbuffer.new
       puts = function(buf, str)
          buf:put(str)
       end
       render = function(buf)
          return buf:get()
       end
    else
       buffnew = function()
          return { n = 0 }
       end
       puts = function(buf, str)
          buf.n = buf.n + 1
          buf[buf.n] = str
       end
       render = function(buf)
          return table.concat(buf)
       end
    end

    local _rawget
    if rawget then
       _rawget = rawget
    else
       _rawget = function(t, k) return t[k] end
    end

    local function rawpairs(t)
       return next, t, nil
    end



    local function smartQuote(str)
       if match(str, '"') and not match(str, "'") then
          return "'" .. str .. "'"
       end
       return '"' .. gsub(str, '"', '\\"') .. '"'
    end


    local shortControlCharEscapes = {
       ["\a"] = "\\a", ["\b"] = "\\b", ["\f"] = "\\f", ["\n"] = "\\n",
       ["\r"] = "\\r", ["\t"] = "\\t", ["\v"] = "\\v", ["\127"] = "\\127",
    }
    local longControlCharEscapes = { ["\127"] = "\127" }
    for i = 0, 31 do
       local ch = char(i)
       if not shortControlCharEscapes[ch] then
          shortControlCharEscapes[ch] = "\\" .. i
          longControlCharEscapes[ch] = fmt("\\%03d", i)
       end
    end

    local function escape(str)
       return (gsub(gsub(gsub(str, "\\", "\\\\"),
       "(%c)%f[0-9]", longControlCharEscapes),
       "%c", shortControlCharEscapes))
    end

    local luaKeywords = {}
    for k in ([[ and break do else elseif end false for function goto if
                 in local nil not or repeat return then true until while
    ]]):gmatch('%w+') do
       luaKeywords[k] = true
    end

    local function isIdentifier(str)
       return type(str) == "string" and
       not not str:match("^[_%a][_%a%d]*$") and
       not luaKeywords[str]
    end

    local flr = math.floor
    local function isSequenceKey(k, sequenceLength)
       return type(k) == "number" and
       flr(k) == k and
       1 <= (k) and
       k <= sequenceLength
    end

    local defaultTypeOrders = {
       ['number'] = 1, ['boolean'] = 2, ['string'] = 3, ['table'] = 4,
       ['function'] = 5, ['userdata'] = 6, ['thread'] = 7,
    }

    local function sortKeys(a, b)
       local ta, tb = type(a), type(b)


       if ta == tb and (ta == 'string' or ta == 'number') then
          return (a) < (b)
       end

       local dta = defaultTypeOrders[ta] or 100
       local dtb = defaultTypeOrders[tb] or 100


       return dta == dtb and ta < tb or dta < dtb
    end

    local function getKeys(t)

       local seqLen = 1
       while _rawget(t, seqLen) ~= nil do
          seqLen = seqLen + 1
       end
       seqLen = seqLen - 1

       local keys, keysLen = {}, 0
       for k in rawpairs(t) do
          if not isSequenceKey(k, seqLen) then
             keysLen = keysLen + 1
             keys[keysLen] = k
          end
       end
       table.sort(keys, sortKeys)
       return keys, keysLen, seqLen
    end

    local function countCycles(x, cycles, depth)
       if type(x) == "table" then
          if cycles[x] then
             cycles[x] = cycles[x] + 1
          else
             cycles[x] = 1
             if depth > 0 then
                for k, v in rawpairs(x) do
                   countCycles(k, cycles, depth - 1)
                   countCycles(v, cycles, depth - 1)
                end
                countCycles(getmetatable(x), cycles, depth - 1)
             end
          end
       end
    end

    local function makePath(path, a, b)
       local newPath = {}
       local len = #path
       for i = 1, len do newPath[i] = path[i] end

       newPath[len + 1] = a
       newPath[len + 2] = b

       return newPath
    end


    local function processRecursive(process,
       item,
       path,
       visited)
       if item == nil then return nil end
       if visited[item] then return visited[item] end

       local processed = process(item, path)
       if type(processed) == "table" then
          local processedCopy = {}
          visited[item] = processedCopy
          local processedKey

          for k, v in rawpairs(processed) do
             processedKey = processRecursive(process, k, makePath(path, k, inspect.KEY), visited)
             if processedKey ~= nil then
                processedCopy[processedKey] = processRecursive(process, v, makePath(path, processedKey), visited)
             end
          end

          local mt = processRecursive(process, getmetatable(processed), makePath(path, inspect.METATABLE), visited)
          if type(mt) ~= 'table' then mt = nil end
          setmetatable(processedCopy, mt)
          processed = processedCopy
       end
       return processed
    end



    local Inspector = {}










    local Inspector_mt = { __index = Inspector }

    local function tabify(inspector)
       puts(inspector.buf, inspector.newline .. rep(inspector.indent, inspector.level))
    end

    function Inspector:getId(v)
       local id = self.ids[v]
       local ids = self.ids
       if not id then
          local tv = type(v)
          id = (ids[tv] or 0) + 1
          ids[v], ids[tv] = id, id
       end
       return tostring(id)
    end

    function Inspector:putValue(v)
       local buf = self.buf
       local tv = type(v)
       if tv == 'string' then
          puts(buf, smartQuote(escape(v)))
       elseif tv == 'number' or tv == 'boolean' or tv == 'nil' or
          tv == 'cdata' or tv == 'ctype' then
          puts(buf, tostring(v))
       elseif tv == 'table' and not self.ids[v] then
          local t = v

          if t == inspect.KEY or t == inspect.METATABLE then
             puts(buf, tostring(t))
          elseif self.level >= self.depth then
             puts(buf, '{...}')
          else
             if self.cycles[t] > 1 then puts(buf, fmt('<%d>', self:getId(t))) end

             local keys, keysLen, seqLen = getKeys(t)

             puts(buf, '{')
             self.level = self.level + 1

             for i = 1, seqLen + keysLen do
                if i > 1 then puts(buf, ',') end
                if i <= seqLen then
                   puts(buf, ' ')
                   self:putValue(t[i])
                else
                   local k = keys[i - seqLen]
                   tabify(self)
                   if isIdentifier(k) then
                      puts(buf, k)
                   else
                      puts(buf, "[")
                      self:putValue(k)
                      puts(buf, "]")
                   end
                   puts(buf, ' = ')
                   self:putValue(t[k])
                end
             end

             local mt = getmetatable(t)
             if type(mt) == 'table' then
                if seqLen + keysLen > 0 then puts(buf, ',') end
                tabify(self)
                puts(buf, '<metatable> = ')
                self:putValue(mt)
             end

             self.level = self.level - 1

             if keysLen > 0 or type(mt) == 'table' then
                tabify(self)
             elseif seqLen > 0 then
                puts(buf, ' ')
             end

             puts(buf, '}')
          end

       else
          puts(buf, fmt('<%s %d>', tv, self:getId(v)))
       end
    end




    function inspect.inspect(root, options)
       options = options or {}

       local depth = options.depth or (math.huge)
       local newline = options.newline or '\n'
       local indent = options.indent or '  '
       local process = options.process

       if process then
          root = processRecursive(process, root, {}, {})
       end

       local cycles = {}
       countCycles(root, cycles, depth)

       local inspector = setmetatable({
          buf = buffnew(),
          ids = {},
          cycles = cycles,
          depth = depth,
          level = 0,
          newline = newline,
          indent = indent,
       }, Inspector_mt)

       inspector:putValue(root)

       return render(inspector.buf)
    end

    setmetatable(inspect, {
       __call = function(_, root, options)
          return inspect.inspect(root, options)
       end,
    })

    return inspect
end)()

-- Removes indentation from readable multiline expectations.
local function unindent(value)
    value = value:gsub(" +$", ""):gsub("^ +", "")

    local minimum = math.huge
    local prefix = ""
    for spaces in value:gmatch("\n( +)") do
        if #spaces < minimum then
            minimum = #spaces
            prefix = spaces
        end
    end

    return (value:gsub("\n" .. prefix, "\n"):gsub("\n$", ""))
end

-- Compares values used by inspect's process callback tests.
local function same(actual, expected, seen)
    if actual == expected then
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

-- Runs one named inspect assertion group.
local function check(name, test)
    local ok, err = pcall(test)
    assert(ok, name .. ": " .. tostring(err))
end

check("primitive values", function()
    assert(inspect(1) == "1")
    assert(inspect(1.5) == "1.5")
    assert(inspect(-3.14) == "-3.14")
    assert(inspect(nil) == "nil")
    assert(inspect(true) == "true")
    assert(inspect(false) == "false")
    assert(inspect("hello") == '"hello"')
    assert(inspect('I have "quotes"') == "'I have \"quotes\"'")
    assert(inspect("I have \"quotes\" and 'apostrophes'") == '"I have \\\"quotes\\\" and \'apostrophes\'"')
end)

check("string escaping", function()
    assert(inspect("I have \n new \n lines") == '"I have \\n new \\n lines"')
    assert(inspect("I have \t a tab") == '"I have \\t a tab"')
    assert(inspect("I have \b a backspace") == '"I have \\b a backspace"')
    assert(inspect("control: \0 \1 \6 \17 \27 \31") == '"control: \\0 \\1 \\6 \\17 \\27 \\31"')
    assert(inspect("DEL: \127") == '"DEL: \\127"')
    assert(inspect("backslash \\\\ followed by text") == '"backslash \\\\\\\\ followed by text"')
end)

check("arrays and dictionaries", function()
    assert(inspect({ 1, 2, 3 }) == "{ 1, 2, 3 }")
    assert(inspect({ "a", "b", "c", { "d", "e" }, "f" }) == '{ "a", "b", "c", { "d", "e" }, "f" }')
    assert(inspect({ a = 1, b = 2 }) == "{\n  a = 1,\n  b = 2\n}")
    assert(inspect({ d = 3, b = { c = 2 }, a = 1 }) == unindent([[
        {
          a = 1,
          b = {
            c = 2
          },
          d = 3
        }
    ]]))
    assert(inspect({ 1, 2, [-1] = true }) == "{ 1, 2,\n  [-1] = true\n}")
    assert(inspect({ ["if"] = true, ["key with spaces"] = true }) == unindent([[
        {
          ["if"] = true,
          ["key with spaces"] = true
        }
    ]]))
end)

check("hybrid and nested tables", function()
    assert(inspect({ "a", { b = 1 }, 2, c = 3, ["ahoy you"] = 4 }) == unindent([[
        { "a", {
            b = 1
          }, 2,
          ["ahoy you"] = 4,
          c = 3
        }
    ]]))

    local table_with_cycle = { 1, 2, 3 }
    local nested = { "a", "b", table_with_cycle }
    table_with_cycle[4] = nested
    table_with_cycle[5] = table_with_cycle
    table_with_cycle[6] = nested
    assert(inspect(table_with_cycle) == '<1>{ 1, 2, 3, <2>{ "a", "b", <table 1> }, <table 1>, <table 2> }')
end)

check("function and special keys", function()
    assert(inspect({ print, type, print }) == "{ <function 1>, <function 2>, <function 1> }")

    local table_with_keys = {
        1,
        2,
        3,
        ["buy more"] = 1,
        a = 1,
        [14] = 1,
        [true] = 1,
    }
    assert(inspect(table_with_keys) == unindent([[
        { 1, 2, 3,
          [14] = 1,
          [true] = 1,
          a = 1,
          ["buy more"] = 1
        }
    ]]))
end)

check("depth and formatting options", function()
    local value = { 1, 2, 3, a = { b = { c = { d = { e = 5 } } } } }

    assert(inspect(value, { depth = 0 }) == "{...}")
    assert(inspect(value, { depth = 1 }) == unindent([[
        { 1, 2, 3,
          a = {...}
        }
    ]]))
    assert(inspect(value, { depth = 2 }) == unindent([[
        { 1, 2, 3,
          a = {
            b = {...}
          }
        }
    ]]))
    assert(inspect({ a = { b = 1 } }, { newline = "@" }) == "{@  a = {@    b = 1@  }@}")
    assert(inspect({ a = { b = 1 } }, { indent = ">>>" }) == "{\n>>>a = {\n>>>>>>b = 1\n>>>}\n}")
end)

check("process callback", function()
    local names = { "Andrew", "Peter", "Ann" }
    assert(inspect(names, { process = function(item) if item ~= "Ann" then return item end end }) == '{ "Andrew", "Peter" }')
    assert(inspect(names, { process = function(item, path) if path[1] ~= 3 then return item end end }) == '{ "Andrew", "Peter" }')
    assert(inspect(names, { process = function(item) return item == "Ann" and "<filtered>" or item end }) == '{ "Andrew", "Peter", "<filtered>" }')

    local dictionary = { a = 1, b = 2 }
    assert(inspect(dictionary, { process = function(item) return item ~= "a" and item or nil end }) == "{\n  b = 2\n}")

    local table_with_metatable = setmetatable({ "hello" }, { "world" })
    assert(inspect(table_with_metatable, {
        process = function(item)
            if item ~= getmetatable(table_with_metatable) then
                return item
            end
        end,
    }) == '{ "hello" }')

    local key_and_metatable = { inspect.KEY, inspect.METATABLE }
    assert(inspect(key_and_metatable) == "{ inspect.KEY, inspect.METATABLE }")

    local items = {}
    local value = { [{ a = 1 }] = setmetatable({ b = 2 }, { c = 3 }) }
    inspect(value, {
        process = function(item, path)
            table.insert(items, { item = item, path = path })
            return item
        end,
    })

    assert(#items == 10)
    assert(items[1].item == value and #items[1].path == 0)
    assert(items[2].path[2] == inspect.KEY)
    assert(items[5].path[1] ~= nil and #items[5].path == 1)
    assert(items[8].path[2] == inspect.METATABLE)
end)

check("metatables", function()
    local metatable = { foo = 1, __mode = "v" }
    local value = setmetatable({ a = 1 }, metatable)
    assert(inspect(value) == unindent([[
        {
          a = 1,
          <metatable> = {
            __mode = "v",
            foo = 1
          }
        }
    ]]))

    local self = {}
    setmetatable(self, self)
    self.__index = self
    assert(inspect(self) == unindent([[
        <1>{
          __index = <table 1>,
          <metatable> = <table 1>
        }
    ]]))

    local tostring_value = setmetatable({ x = 1 }, {
        __tostring = function(value)
            return inspect(value)
        end,
    })
    assert(tostring(tostring_value) == unindent([[
        {
          x = 1,
          <metatable> = {
            __tostring = <function 1>
          }
        }
    ]]))
end)

check("callable and explicit interfaces", function()
    assert(inspect({}) == "{}")
    assert(inspect.inspect({}) == "{}")
end)

print("inspect: ok")
