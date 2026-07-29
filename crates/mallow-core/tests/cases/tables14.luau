local Base = {}
Base.__index = Base
function Base:kind() return "base" end

local Child = setmetatable({}, { __index = Base })
Child.__index = Child
function Child:name() return "child" end

local obj = setmetatable({}, Child)
assert(obj:name() == "child")
assert(obj:kind() == "base") -- walks the chain
