local Disk = (function()
    type Set__DARKLUA_TYPE_a<T> ={[T]:true}

    type reduceFromFirstValue__DARKLUA_TYPE_b=<T>(
    array:{T},
    reducer:(accumulator:T,value:T,index:number)->T
    )->T?

    type reduceWithAccumulator__DARKLUA_TYPE_c=<T,A>(
    array:{T},
    reducer:(accumulator:A,value:T,index:number)->A,
    accumulator:A
    )->A

    type alternate1__DARKLUA_TYPE_d=<A>({A})->{A}

    type alternate2__DARKLUA_TYPE_e=<A,B>({A},{B})->{A|B}

    type alternate3__DARKLUA_TYPE_f=<A,B,C>({A},{B},{C})->{A|B|C}

    type alternateAll__DARKLUA_TYPE_g=<T,U,V...>({T},V...)->{U}

    type BinarySearchFn__DARKLUA_TYPE_h=
    ((array:{number|string},value:number|string)->number?)
    &(<T>(array:{T},value:T,compareFn:(a:T,b:T)->number)->number?)

    type KeyElement__DARKLUA_TYPE_i<K,V> ={key:K,element:V}

    type zip1__DARKLUA_TYPE_j=<A>({A})->{{A}}

    type zip2__DARKLUA_TYPE_k=<A,B>({A},{B})->{{A|B}}

    type zip3__DARKLUA_TYPE_l=<A,B,C>({A},{B},{C})->{{A|B|C}}

    type zipAll__DARKLUA_TYPE_m=<T,U>({T},...{U})->{{T|U}}

    type EntriesFn__DARKLUA_TYPE_n=
    (<K,V>(map:{[K]:V})->{{K|V}})
    &(<K,V,T,U>(map:{[K]:V},keyIndex:T,valueIndex:U)->{{[(T|U)]:K|V}})

    type FromEntriesFn__DARKLUA_TYPE_o=
    (<K,V>(entries:{{K|V}})->{[K]:V})
    &(<K,V,T>(entries:{{[T]:K|V}},keyIndex:T,valueIndex:T)->{[K]:V})

    type merge1__DARKLUA_TYPE_p=<A>(A)->A

    type merge2__DARKLUA_TYPE_q=<A,B>(A,B)->A&B

    type merge3__DARKLUA_TYPE_r=<A,B,C>(A,B,C)->A&B&C

    type merge4__DARKLUA_TYPE_s=<A,B,C,D>(A,B,C,D)->A&B&C&D

    type merge5__DARKLUA_TYPE_t=<A,B,C,D,E>(A,B,C,D,E)->A&B&C&D&E

    type mergeAll__DARKLUA_TYPE_u=<T,U,V...>(T,V...)->U

    type Set__DARKLUA_TYPE_v<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_w<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_x<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_y<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_z<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_A<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_B<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_C<T> =Set__DARKLUA_TYPE_a<T>

    type Set__DARKLUA_TYPE_D<T> =Set__DARKLUA_TYPE_a<T>local __DARKLUA_BUNDLE_MODULES={cache={}::any}do do local function __modImpl()



    return nil end function __DARKLUA_BUNDLE_MODULES.a():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.a if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.a=v end return v.c end end do local function __modImpl()

    local function all<T>(array:{T},predicate:(element:T,index:number)->boolean):boolean
    for index,element in array do
    if not predicate(element,index)then
    return false
    end
    end
    return true
    end

    return all end function __DARKLUA_BUNDLE_MODULES.b():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.b if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.b=v end return v.c end end do local function __modImpl()

    local function reduce<T,A>(
    array:{T},
    reducer:(accumulator:A,value:T,index:number)->A,
    accumulator:A?
    ):A
    if accumulator==nil then
    for index,value in array do
    if index==1 then
    accumulator=value::any
    else
    accumulator=reducer(accumulator::A,value,index)
    end
    end
    else
    for index,value in array do
    accumulator=reducer(accumulator,value,index)
    end
    end
    return accumulator::A
    end











    return(reduce::any)::reduceFromFirstValue__DARKLUA_TYPE_b&reduceWithAccumulator__DARKLUA_TYPE_c end function __DARKLUA_BUNDLE_MODULES.c():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.c if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.c=v end return v.c end end do local function __modImpl()

    local reduce=__DARKLUA_BUNDLE_MODULES.c()

    local function alternate<T,U>(array:{T},...:{U}):{any}
    local alternateWith={...}

    if#alternateWith==0 then
    return array
    end

    local minimumLength=reduce(alternateWith,function(minimum:number,value)
    return math.min(minimum,#value)
    end,#array)

    if minimumLength==0 then
    return{}
    end

    local result={}

    for i=1,minimumLength do
    table.insert(result,array[i])
    for _,otherArray in alternateWith do
    table.insert(result,otherArray[i]::any)
    end
    end

    return result
    end






    return(alternate::any)::alternate1__DARKLUA_TYPE_d&alternate2__DARKLUA_TYPE_e&alternate3__DARKLUA_TYPE_f&alternateAll__DARKLUA_TYPE_g end function __DARKLUA_BUNDLE_MODULES.d():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.d if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.d=v end return v.c end end do local function __modImpl()

    local function any<T>(array:{T},predicate:(element:T,index:number)->boolean):boolean
    for index,element in array do
    if predicate(element,index)then
    return true
    end
    end
    return false
    end

    return any end function __DARKLUA_BUNDLE_MODULES.e():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.e if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.e=v end return v.c end end do local function __modImpl()

    local function average(array:{number}):number?
    local length=#array
    if length==0 then
    return nil
    end

    local result=0

    for _,element in array do
    result+=element
    end

    return result/length
    end

    return average end function __DARKLUA_BUNDLE_MODULES.f():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.f if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.f=v end return v.c end end do local function __modImpl()

    local function averageBy<T>(array:{T},map:(T)->number):number?
    local length=#array
    if length==0 then
    return nil
    end

    local result=0

    for _,element in array do
    result+=map(element)
    end

    return result/length
    end

    return averageBy end function __DARKLUA_BUNDLE_MODULES.g():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.g if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.g=v end return v.c end end do local function __modImpl()

    local function binarySearch<T>(array:{T},value:T,compareFn:((a:T,b:T)->number)?):number?
    local length=#array
    if length==0 then
    return nil
    end

    local left=1
    local right=length

    if compareFn==nil then
    while left<=right do
    local mid=math.floor((left+right)/2)
    local midElement=array[mid]::any

    if midElement<value then
    left=mid+1
    elseif midElement>value then
    right=mid-1
    else
    return mid
    end
    end

    return nil
    end

    while left<=right do
    local mid=math.floor((left+right)/2)
    local comparison=compareFn(array[mid],value)

    if comparison==0 then
    return mid
    elseif comparison<0 then
    left=mid+1
    else
    right=mid-1
    end
    end

    return nil
    end





    return(binarySearch::any)::BinarySearchFn__DARKLUA_TYPE_h end function __DARKLUA_BUNDLE_MODULES.h():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.h if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.h=v end return v.c end end do local function __modImpl()

    local function binarySearchByKey<T,K>(array:{T},value:K,keyFn:(element:T)->K):number?
    local length=#array
    if length==0 then
    return nil
    end

    local left=1
    local right=length

    while left<=right do
    local mid=math.floor((left+right)/2)
    local midElement=keyFn(array[mid])::any

    if midElement<value then
    left=mid+1
    elseif midElement>value then
    right=mid-1
    else
    return mid
    end
    end

    return nil
    end

    return binarySearchByKey end function __DARKLUA_BUNDLE_MODULES.i():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.i if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.i=v end return v.c end end do local function __modImpl()

    local function chunks<T>(array:{T},size:number):{{T}}
    size=math.round(size)
    local length=#array

    if size<=0 then
    error('chunk size must be greater than 0')
    elseif length==0 then
    return{}
    elseif size==1 then
    local result=table.create(length)
    for _,value in array do
    table.insert(result,{value})
    end
    return result
    elseif size>=length then
    return{array}
    end

    local result=table.create(math.ceil(length/size))
    local currentChunk=table.create(size)
    local currentSize=0

    for _,value in array do
    table.insert(currentChunk,value)
    currentSize+=1

    if currentSize==size then
    table.insert(result,currentChunk)
    currentChunk=table.create(size)
    currentSize=0
    end
    end

    if currentSize~=0 then
    table.insert(result,currentChunk)
    end

    return result
    end

    return chunks end function __DARKLUA_BUNDLE_MODULES.j():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.j if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.j=v end return v.c end end do local function __modImpl()

    local function concat<T>(array:{T},...:{T}?):{T}
    local result

    for i=1,select('#',...)do
    local concatWith=select(i,...)

    if concatWith~=nil and#concatWith>0 then
    result=result or table.clone(array)

    for _,element in concatWith do
    table.insert(result,element)
    end
    end
    end

    return result or array
    end

    return concat end function __DARKLUA_BUNDLE_MODULES.k():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.k if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.k=v end return v.c end end do local function __modImpl()

    local function contains<T>(array:{T},element:T):boolean
    for _,value in array do
    if value==element then
    return true
    end
    end
    return false
    end

    return contains end function __DARKLUA_BUNDLE_MODULES.l():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.l if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.l=v end return v.c end end do local function __modImpl()

    return table.clone end function __DARKLUA_BUNDLE_MODULES.m():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.m if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.m=v end return v.c end end do local function __modImpl()

    local function count<T>(array:{T},predicate:((T,number)->boolean)?):number
    if predicate==nil then
    return#array
    end

    local total=0

    for i,element in array do
    if predicate(element,i)then
    total+=1
    end
    end

    return total
    end

    return count end function __DARKLUA_BUNDLE_MODULES.n():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.n if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.n=v end return v.c end end do local function __modImpl()

    local function deduplicate<T>(array:{T}):{T}
    if#array==0 then
    return array
    end

    local removeIndexes={}

    local seenSet={}

    for index,element in array do
    if seenSet[element]==nil then
    seenSet[element]=true
    else
    table.insert(removeIndexes,index)
    end
    end

    local totalIndexes=#removeIndexes
    if totalIndexes==0 then
    return array
    else
    local result=table.clone(array)
    for i=totalIndexes,1,-1 do
    table.remove(result,removeIndexes[i])
    end
    return result
    end
    end

    return deduplicate end function __DARKLUA_BUNDLE_MODULES.o():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.o if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.o=v end return v.c end end do local function __modImpl()

    local function deduplicateByKey<T,Comparable>(array:{T},key:(T)->Comparable):{T}
    local removeIndexes={}

    local seenSet={}

    for index,element in array do
    local elementKey=key(element)
    if seenSet[elementKey]==nil then
    seenSet[elementKey]=true
    else
    table.insert(removeIndexes,index)
    end
    end

    local totalIndexes=#removeIndexes
    if totalIndexes==0 then
    return array
    else
    local result=table.clone(array)
    for i=totalIndexes,1,-1 do
    table.remove(result,removeIndexes[i])
    end
    return result
    end
    end

    return deduplicateByKey end function __DARKLUA_BUNDLE_MODULES.p():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.p if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.p=v end return v.c end end do local function __modImpl()

    local function removeSortedIndexes<T>(array:{T},indexes:{number}):{T}
    local removeLength=#indexes
    local arrayLenth=#array

    if removeLength==0 or arrayLenth==0 then
    return array
    end

    local startFrom
    for i=removeLength,1,-1 do
    local index=indexes[i]
    if index<=arrayLenth then
    startFrom=index
    break
    end
    end

    if startFrom==nil then
    return array
    else
    local cloned=table.clone(array)
    local length=arrayLenth

    local previous
    for i=startFrom,1,-1 do
    local index=indexes[i]
    if index~=previous and index<=length then
    length-=1
    table.remove(cloned,index)
    previous=index
    end
    end

    return cloned
    end
    end

    return removeSortedIndexes end function __DARKLUA_BUNDLE_MODULES.q():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.q if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.q=v end return v.c end end do local function __modImpl()

    local removeSortedIndexes=__DARKLUA_BUNDLE_MODULES.q()

    local function difference<T>(array:{T},...:{T}?):{T}
    local arrayCount=select('#',...)
    local arrayLength=#array

    if arrayCount==0 or arrayLength==0 then
    return array
    end

    local otherArrays={}

    for i=1,arrayCount do
    local otherArray=select(i,...)
    if otherArray~=nil and#otherArray~=0 then
    table.insert(otherArrays,otherArray)
    end
    end

    if#otherArrays==0 then
    return array
    end

    local indexes={}

    for index,element in array do
    for _,otherArray in otherArrays do
    if table.find(otherArray,element)then
    table.insert(indexes,index)
    break
    end
    end
    end

    local totalIndexes=#indexes

    if totalIndexes==0 then
    return array
    elseif totalIndexes==arrayLength then
    return{}
    else
    return removeSortedIndexes(array,indexes)
    end
    end

    return difference end function __DARKLUA_BUNDLE_MODULES.r():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.r if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.r=v end return v.c end end do local function __modImpl()

    local difference=__DARKLUA_BUNDLE_MODULES.r()
    local removeSortedIndexes=__DARKLUA_BUNDLE_MODULES.q()

    local function differenceSymmetric<T>(array:{T},...:{T}):{T}
    local arrayCount=select('#',...)

    if arrayCount==0 then
    return array
    end

    local otherArrays={}

    for i=1,arrayCount do
    local otherArray=select(i,...)
    if otherArray and#otherArray~=0 then
    table.insert(otherArrays,otherArray)
    end
    end

    local indexes={}

    for index,element in array do
    for _,otherArray in otherArrays do
    if table.find(otherArray,element)then
    table.insert(indexes,index)
    break
    end
    end
    end

    local finalResult

    if#indexes~=0 then
    finalResult=table.clone(array)

    for i=#indexes,1,-1 do
    local index=indexes[i]
    table.remove(finalResult,index)
    end
    end

    for arrayIndex,otherArray in otherArrays do
    local others=removeSortedIndexes(otherArrays,{arrayIndex})
    table.insert(others,array)

    local result=difference(otherArray,unpack(others))

    if#result~=0 then
    if finalResult==nil then
    finalResult=table.clone(array)
    end

    for _,value in result do
    table.insert(finalResult,value)
    end
    end
    end

    return finalResult or array
    end

    return differenceSymmetric end function __DARKLUA_BUNDLE_MODULES.s():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.s if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.s=v end return v.c end end do local function __modImpl()

    local function filter<T>(array:{T},predicate:(T,number)->boolean):{T}
    local new={}
    for i,element in array do
    if predicate(element,i)then
    table.insert(new,element)
    end
    end
    return new
    end

    return filter end function __DARKLUA_BUNDLE_MODULES.t():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.t if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.t=v end return v.c end end do local function __modImpl()

    local function find<T>(
    array:{T},
    predicate:(element:T,index:number)->boolean,
    start:number?
    ):T?
    if start==nil or start==1 then
    for index,element in array do
    if predicate(element,index)then
    return element
    end
    end
    else
    local length=#array
    for i=start,length do
    local element=array[i]
    if predicate(element,i)then
    return element
    end
    end
    end

    return nil
    end

    return find end function __DARKLUA_BUNDLE_MODULES.u():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.u if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.u=v end return v.c end end do local function __modImpl()

    local function findClosest(array:{number},target:number,start:number?):number?
    local length=#array
    if length==0 then
    return nil
    elseif length==1 then
    return array[1]
    end

    local closestIndex
    local closest

    if start==nil or start==1 then
    for index,element in array do
    local distance=math.abs(element-target)
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=index
    end
    end
    else
    for i=start,length do
    local element=array[i]
    local distance=math.abs(element-target)
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=i
    end
    end
    end

    return if closestIndex then array[closestIndex]else nil
    end

    return findClosest end function __DARKLUA_BUNDLE_MODULES.v():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.v if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.v=v end return v.c end end do local function __modImpl()

    local function findClosestBy<T>(array:{T},getDistance:(element:T)->number,start:number?):T?
    local length=#array
    if length==0 then
    return nil
    elseif length==1 then
    return array[1]
    end

    local closestIndex
    local closest

    if start==nil or start==1 then
    for index,element in array do
    local distance=math.abs(getDistance(element))
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=index
    end
    end
    else
    for i=start,length do
    local element=array[i]
    local distance=math.abs(getDistance(element))
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=i
    end
    end
    end

    return if closestIndex then array[closestIndex]else nil
    end

    return findClosestBy end function __DARKLUA_BUNDLE_MODULES.w():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.w if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.w=v end return v.c end end do local function __modImpl()

    local function findClosest(array:{number},target:number,start:number?):number?
    local length=#array
    if length==0 then
    return nil
    elseif length==1 then
    return 1
    end

    local closestIndex
    local closest

    if start==nil or start==1 then
    for index,element in array do
    local distance=math.abs(element-target)
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=index
    end
    end
    else
    for i=start,length do
    local element=array[i]
    local distance=math.abs(element-target)
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=i
    end
    end
    end

    return closestIndex
    end

    return findClosest end function __DARKLUA_BUNDLE_MODULES.x():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.x if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.x=v end return v.c end end do local function __modImpl()

    local function findClosestIndexBy<T>(
    array:{T},
    getDistance:(element:T)->number,
    start:number?
    ):number?
    local length=#array
    if length==0 then
    return nil
    elseif length==1 then
    return 1
    end

    local closestIndex
    local closest

    if start==nil or start==1 then
    for index,element in array do
    local distance=math.abs(getDistance(element))
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=index
    end
    end
    else
    for i=start,length do
    local element=array[i]
    local distance=math.abs(getDistance(element))
    if closest==nil or distance<closest then
    closest=distance
    closestIndex=i
    end
    end
    end

    return closestIndex
    end

    return findClosestIndexBy end function __DARKLUA_BUNDLE_MODULES.y():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.y if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.y=v end return v.c end end do local function __modImpl()

    local function findIndex<T>(
    array:{T},
    predicate:(element:T,index:number)->boolean,
    start:number?
    ):number?
    if start==nil or start==1 then
    for index,element in array do
    if predicate(element,index)then
    return index
    end
    end
    else
    local length=#array
    for i=start,length do
    local element=array[i]
    if predicate(element,i)then
    return i
    end
    end
    end

    return nil
    end

    return findIndex end function __DARKLUA_BUNDLE_MODULES.z():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.z if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.z=v end return v.c end end do local function __modImpl()

    local function findIndexByValue<T>(array:{T},element:T,start:number?):number?
    return table.find(array,element,start)
    end

    return findIndexByValue end function __DARKLUA_BUNDLE_MODULES.A():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.A if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.A=v end return v.c end end do local function __modImpl()

    local function findMap<T,U>(array:{T},mapFn:(element:T,index:number)->U?,start:number?):U?
    if start==nil or start==1 then
    for index,element in array do
    local result=mapFn(element,index)
    if result~=nil then
    return result
    end
    end
    else
    local length=#array
    for i=start,length do
    local element=array[i]
    local result=mapFn(element,i)
    if result~=nil then
    return result
    end
    end
    end

    return nil
    end

    return findMap end function __DARKLUA_BUNDLE_MODULES.B():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.B if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.B=v end return v.c end end do local function __modImpl()

    local function isArray(value:unknown):boolean
    if type(value)~='table'then
    return false
    end

    local tableValue:{[any]:any}=value::any

    if next(tableValue)==nil then

    return true
    end

    local length=#tableValue

    if length==0 then
    return false
    end

    local expectIndex=0

    for key in tableValue do
    expectIndex+=1
    if type(key)~='number'or key~=expectIndex then
    return false
    end
    end

    return length==expectIndex
    end

    return isArray end function __DARKLUA_BUNDLE_MODULES.C():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.C if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.C=v end return v.c end end do local function __modImpl()

    local isArray=__DARKLUA_BUNDLE_MODULES.C()

    local function flatMap<T,U>(array:{T},mapFn:(T,number)->nil|U|{U}):{U}
    local new={}
    for i,element in array do
    local value=mapFn(element,i)
    if value~=nil then
    if isArray(value)then
    for _,innerElement in value::{U}do
    table.insert(new,innerElement)
    end
    else
    table.insert(new,value::U)
    end
    end
    end
    return new
    end

    return flatMap end function __DARKLUA_BUNDLE_MODULES.D():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.D if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.D=v end return v.c end end do local function __modImpl()

    local isArray=__DARKLUA_BUNDLE_MODULES.C()

    local function flatten<T>(array:{T|{T}},depth:number?):{T}
    local actualDepth=if depth==nil then math.huge else depth
    if actualDepth<=0 then
    return array::{T}
    end

    local new={}

    for _,element in array do
    if isArray(element)then
    local iter:{T}=if actualDepth>1
    then flatten(element::{T},actualDepth-1)
    else element::{T}
    for _,innerElement in iter do
    table.insert(new,innerElement)
    end
    else
    table.insert(new,element::T)
    end
    end

    return new
    end

    return flatten end function __DARKLUA_BUNDLE_MODULES.E():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.E if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.E=v end return v.c end end do local function __modImpl()

    local function fromFn<T>(generator:(number)->T?):{T}
    local array={}

    local i=1
    while true do
    local element=generator(i)
    if element==nil then
    break
    else
    i+=1
    table.insert(array,element)
    end
    end

    return array
    end

    return fromFn end function __DARKLUA_BUNDLE_MODULES.F():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.F if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.F=v end return v.c end end do local function __modImpl()

    local function fromTryFn<T>(generator:(number)->T?):{T}
    local array={}

    local i=1
    while true do
    local success,element=pcall(generator,i)
    if success==false or element==nil then
    break
    else
    i+=1
    table.insert(array,element)
    end
    end

    return array
    end

    return fromTryFn end function __DARKLUA_BUNDLE_MODULES.G():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.G if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.G=v end return v.c end end do local function __modImpl()

    local findIndex=__DARKLUA_BUNDLE_MODULES.z()

    local function insertAfter<T>(
    array:{T},
    value:T,
    predicate:(element:T)->boolean,
    start:number?
    ):{T}
    local index=findIndex(array,predicate,start)

    if not index then
    return array
    end

    local copy=table.clone(array)

    if index==#array then
    table.insert(copy,value)
    else
    table.insert(copy,index+1,value)
    end

    return copy
    end

    return insertAfter end function __DARKLUA_BUNDLE_MODULES.H():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.H if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.H=v end return v.c end end do local function __modImpl()

    local function insertAfterIndex<T>(array:{T},value:T,index:number):{T}
    local copy=table.clone(array)
    local length=#copy


    index+=1

    if index<1 then
    table.insert(copy,1,value)
    elseif index>length then
    table.insert(copy,value)
    else
    table.insert(copy,index,value)
    end

    return copy
    end

    return insertAfterIndex end function __DARKLUA_BUNDLE_MODULES.I():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.I if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.I=v end return v.c end end do local function __modImpl()

    local findIndex=__DARKLUA_BUNDLE_MODULES.z()

    local function insertBefore<T>(
    array:{T},
    value:T,
    predicate:(element:T)->boolean,
    start:number?
    ):{T}
    local index=findIndex(array,predicate,start)

    if not index then
    return array
    end

    local copy=table.clone(array)
    table.insert(copy,index,value)

    return copy
    end

    return insertBefore end function __DARKLUA_BUNDLE_MODULES.J():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.J if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.J=v end return v.c end end do local function __modImpl()

    local function insertBeforeIndex<T>(array:{T},value:T,index:number):{T}
    local copy=table.clone(array)
    local length=#copy

    if index<1 then
    table.insert(copy,1,value)
    elseif index>length then
    table.insert(copy,value)
    else
    table.insert(copy,index,value)
    end

    return copy
    end

    return insertBeforeIndex end function __DARKLUA_BUNDLE_MODULES.K():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.K if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.K=v end return v.c end end do local function __modImpl()

    local function isEmpty(value:{[any]:any}):boolean
    return next(value)==nil
    end

    return isEmpty end function __DARKLUA_BUNDLE_MODULES.L():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.L if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.L=v end return v.c end end do local function __modImpl()

    local function map<T,U>(array:{T},mapFn:(T,number)->U?):{U}
    local new={}
    for i,element in array do
    local value=mapFn(element,i)
    if value~=nil then
    table.insert(new,value)
    end
    end
    return new
    end

    return map end function __DARKLUA_BUNDLE_MODULES.M():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.M if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.M=v end return v.c end end do local function __modImpl()

    local function maximum(array:{number},initialValue:number?):number
    if initialValue==nil then
    if#array==0 then
    error('initial value must be provided to Array.maximum when the array is empty')
    end
    initialValue=array[1]
    end

    local accumulator=initialValue::number
    for _,element in array do
    accumulator=math.max(accumulator,element)
    end
    return accumulator
    end

    return maximum end function __DARKLUA_BUNDLE_MODULES.N():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.N if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.N=v end return v.c end end do local function __modImpl()

    local function maximumBy<T>(array:{T},map:(T)->number,initialValue:number?):number
    if initialValue==nil then
    if#array==0 then
    error('initial value must be provided to Array.maximumBy when the array is empty')
    end
    initialValue=map(array[1])
    end

    local accumulator:number=initialValue::number
    for _,element in array do
    accumulator=math.max(accumulator,map(element))
    end
    return accumulator
    end

    return maximumBy end function __DARKLUA_BUNDLE_MODULES.O():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.O if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.O=v end return v.c end end do local function __modImpl()

    local function minimum(array:{number},initialValue:number?):number
    if initialValue==nil then
    if#array==0 then
    error('initial value must be provided to Array.minimum when the array is empty')
    end
    initialValue=array[1]
    end

    local accumulator=initialValue::number
    for _,element in array do
    accumulator=math.min(accumulator,element)
    end
    return accumulator
    end

    return minimum end function __DARKLUA_BUNDLE_MODULES.P():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.P if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.P=v end return v.c end end do local function __modImpl()

    local function minimumBy<T>(array:{T},map:(T)->number,initialValue:number?):number
    if initialValue==nil then
    if#array==0 then
    error('initial value must be provided to Array.minimumBy when the array is empty')
    end
    initialValue=map(array[1])
    end

    local accumulator:number=initialValue::number
    for _,element in array do
    accumulator=math.min(accumulator,map(element))
    end
    return accumulator
    end

    return minimumBy end function __DARKLUA_BUNDLE_MODULES.Q():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.Q if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.Q=v end return v.c end end do local function __modImpl()

    local function partition<T>(array:{T},predicate:(T,number)->boolean):({T},{T})
    local trueValues={}
    local falseValues={}
    for i,element in array do
    if predicate(element,i)then
    table.insert(trueValues,element)
    else
    table.insert(falseValues,element)
    end
    end
    return trueValues,falseValues
    end

    return partition end function __DARKLUA_BUNDLE_MODULES.R():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.R if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.R=v end return v.c end end do local function __modImpl()

    local isArray=__DARKLUA_BUNDLE_MODULES.C()

    local function pluck<T,U>(array:{T},key:any|{any}):{U}
    local length=#array

    local keys=if isArray(key)then key else{key}

    if#keys==0 then
    return array::any
    end

    local result=table.create(length)

    for _,element in array do
    local indexed:any=element

    local success=pcall(function()
    for _,value in keys do
    indexed=indexed[value]

    if indexed==nil then
    break
    end
    end
    end)

    if not success then
    indexed=nil
    end

    if indexed~=nil then
    table.insert(result,indexed)
    end
    end

    return result::any
    end

    return pluck end function __DARKLUA_BUNDLE_MODULES.S():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.S if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.S=v end return v.c end end do local function __modImpl()

    local function pop<T>(array:{T},count:number?):{T}
    local actualCount=count or 1

    if actualCount==1 then
    local new=table.clone(array)
    table.remove(new)
    return new
    elseif actualCount==0 then
    return array
    else
    local length=#array

    local remaining=length-actualCount

    if remaining<=0 then
    return{}
    elseif remaining>actualCount then
    local new=table.clone(array)

    for _=1,actualCount do
    table.remove(new)
    end

    return new
    else
    local new={}

    for i=1,remaining do
    new[i]=array[i]
    end
    return new
    end
    end
    end

    return pop end function __DARKLUA_BUNDLE_MODULES.T():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.T if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.T=v end return v.c end end do local function __modImpl()

    local function popFirst<T>(array:{T},count:number?):{T}
    local actualCount=count or 1

    if actualCount==1 then
    local new=table.clone(array)
    table.remove(new,1)
    return new
    elseif actualCount==0 then
    return array
    else
    local length=#array

    local remaining=length-actualCount

    if remaining<=0 then
    return{}
    elseif remaining>actualCount then
    local new=table.clone(array)

    for _=1,actualCount do
    table.remove(new,1)
    end

    return new
    else
    local new={}

    for i=1+actualCount,length do
    table.insert(new,array[i])
    end

    return new
    end
    end
    end

    return popFirst end function __DARKLUA_BUNDLE_MODULES.U():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.U if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.U=v end return v.c end end do local function __modImpl()

    local function product(array:{number},initialValue:number?):number
    local result=if initialValue==nil then 1 else initialValue

    for _,element in array do
    result*=element
    end

    return result
    end

    return product end function __DARKLUA_BUNDLE_MODULES.V():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.V if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.V=v end return v.c end end do local function __modImpl()

    local function productBy<T>(array:{T},map:(T)->number,initialValue:number?):number
    local result=if initialValue==nil then 1 else initialValue

    for _,element in array do
    result*=map(element)
    end

    return result
    end

    return productBy end function __DARKLUA_BUNDLE_MODULES.W():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.W if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.W=v end return v.c end end do local function __modImpl()

    local function push<T>(array:{T},...:T?):{T}
    local newArray=table.clone(array)

    for i=1,select('#',...)do
    local element=select(i,...)
    if element~=nil then
    table.insert(newArray,element)
    end
    end

    return newArray
    end

    return push end function __DARKLUA_BUNDLE_MODULES.X():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.X if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.X=v end return v.c end end do local function __modImpl()

    local function range<T>(array:{T},from:number,to:number?):{T}
    local length=#array
    if length==0 then
    return array
    end
    local actualTo=if to==nil then length else to

    local normalizedFrom=if from<0 then 1+(from+length)else from
    local normalizedTo=if actualTo<0 then 1+(actualTo+length)else actualTo

    local result={}

    if normalizedTo>=normalizedFrom then
    for i=math.max(normalizedFrom,1),math.min(normalizedTo,length)do
    table.insert(result,array[i])
    end
    else
    for i=math.min(normalizedFrom,length),math.max(normalizedTo,1),-1 do
    table.insert(result,array[i])
    end
    end

    return result
    end

    return range end function __DARKLUA_BUNDLE_MODULES.Y():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.Y if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.Y=v end return v.c end end do local function __modImpl()

    local function sort<T>(array:{T},comparator:((T,T)->boolean)?):{T}
    if#array<=1 then
    return array
    end
    local result=table.clone(array)
    table.sort(result,comparator)
    return result
    end

    return sort end function __DARKLUA_BUNDLE_MODULES.Z():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.Z if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.Z=v end return v.c end end do local function __modImpl()

    local removeSortedIndexes=__DARKLUA_BUNDLE_MODULES.q()
    local sort=__DARKLUA_BUNDLE_MODULES.Z()

    local function removeIndexes<T>(array:{T},indexes:{number}):{T}
    local removeLength=#indexes
    local arrayLenth=#array

    if removeLength==0 or arrayLenth==0 then
    return array
    end

    local sortedIndexes=sort(indexes)

    return removeSortedIndexes(array,sortedIndexes)
    end

    return removeIndexes end function __DARKLUA_BUNDLE_MODULES._():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache._ if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache._=v end return v.c end end do local function __modImpl()

    local function removeValues<T>(array:{T},...:T?):{T}
    local removeLength=select('#',...)
    local arrayLenth=#array

    if removeLength==0 or arrayLenth==0 then
    return array
    end

    local removeIndexes={}
    for index,element in array do
    for i=1,removeLength do
    local value:T?=select(i,...)

    if value~=nil and element==value then
    table.insert(removeIndexes,index)
    end
    end
    end

    local removeIndexesLength=#removeIndexes

    if removeIndexesLength==0 then
    return array
    elseif removeIndexesLength==arrayLenth then
    return{}
    else
    local cloned=table.clone(array)

    for i=removeIndexesLength,1,-1 do
    table.remove(cloned,removeIndexes[i])
    end

    return cloned
    end
    end

    return removeValues end function __DARKLUA_BUNDLE_MODULES.aa():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aa if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aa=v end return v.c end end do local function __modImpl()

    local isEmpty=__DARKLUA_BUNDLE_MODULES.L()

    local function repeatSequence<T>(array:{T},count:number):{T}
    if count==1 or isEmpty(array)then
    return array
    elseif count<=0 then
    return{}
    end

    local result=table.clone(array)
    local length=#array

    for _=1,count-1 do
    for j=1,length do
    table.insert(result,array[j])
    end
    end

    return result
    end

    return repeatSequence end function __DARKLUA_BUNDLE_MODULES.ab():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ab if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ab=v end return v.c end end do local function __modImpl()

    local function replaceAtIndex<T>(array:{T},index:number,value:T):{T}
    local length=#array

    if index<1 or index>length or array[index]==value then
    return array
    end

    local copy=table.clone(array)
    copy[index]=value

    return copy
    end

    return replaceAtIndex end function __DARKLUA_BUNDLE_MODULES.ac():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ac if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ac=v end return v.c end end do local function __modImpl()

    local function reverse<T>(array:{T}):{T}
    local length=#array

    if length<2 then
    return array
    end

    local newArray=table.clone(array)

    for i=1,math.floor(length/2)do
    local swapRight=length-i+1

    newArray[i],newArray[swapRight]=newArray[swapRight],newArray[i]
    end

    return newArray
    end

    return reverse end function __DARKLUA_BUNDLE_MODULES.ad():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ad if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ad=v end return v.c end end do local function __modImpl()

    local function reverseFind<T>(
    array:{T},
    predicate:(element:T,index:number)->boolean,
    start:number?
    ):T?
    local length=#array

    for i=start or length,1,-1 do
    local element=array[i]
    if predicate(element,i)then
    return element
    end
    end

    return nil
    end

    return reverseFind end function __DARKLUA_BUNDLE_MODULES.ae():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ae if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ae=v end return v.c end end do local function __modImpl()

    local function reverseFindIndex<T>(
    array:{T},
    predicate:(element:T,index:number)->boolean,
    start:number?
    ):number?
    local length=#array

    for i=start or length,1,-1 do
    local element=array[i]
    if predicate(element,i)then
    return i
    end
    end

    return nil
    end

    return reverseFindIndex end function __DARKLUA_BUNDLE_MODULES.af():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.af if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.af=v end return v.c end end do local function __modImpl()

    local function reverseFindIndexByValue<T>(array:{T},element:T,start:number?):number?
    local length=#array

    for i=start or length,1,-1 do
    if array[i]==element then
    return i
    end
    end

    return nil
    end

    return reverseFindIndexByValue end function __DARKLUA_BUNDLE_MODULES.ag():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ag if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ag=v end return v.c end end do local function __modImpl()

    local function reverseFindMap<T,U>(
    array:{T},
    mapFn:(element:T,index:number)->U?,
    start:number?
    ):U?
    local length=#array

    for i=start or length,1,-1 do
    local element=array[i]
    local result=mapFn(element,i)
    if result~=nil then
    return result
    end
    end

    return nil
    end

    return reverseFindMap end function __DARKLUA_BUNDLE_MODULES.ah():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ah if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ah=v end return v.c end end do local function __modImpl()

    local map=__DARKLUA_BUNDLE_MODULES.M()



    local function sortByKey<T,Comparable>(array:{T},key:(T)->Comparable):{T}
    if#array<=1 then
    return array
    end
    local result:{KeyElement__DARKLUA_TYPE_i<Comparable,T>}=map(array,function(element)
    return{
    key=key(element),
    element=element,
    }
    end)

    table.sort(result,function(a:any,b:any)
    return a.key<b.key
    end)

    for index,element in result do
    result[index]=element.element::any
    end

    return result::any
    end

    return sortByKey end function __DARKLUA_BUNDLE_MODULES.ai():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ai if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ai=v end return v.c end end do local function __modImpl()

    local function stepBy<T>(array:{T},step:number):{T}
    local length=#array

    if step==1 then
    return array
    elseif step==-1 then
    local newArray=table.clone(array)

    for i=1,math.floor(length/2)do
    local swapRight=length-i+1

    newArray[i],newArray[swapRight]=newArray[swapRight],newArray[i]
    end

    return newArray
    elseif step>1 then
    local result={}

    for i=1,length,step do
    table.insert(result,array[i])
    end

    return result
    elseif step<-1 then
    local result={}

    for i=length,1,step do
    table.insert(result,array[i])
    end

    return result
    else
    error(`invalid step value '{step}' passed to Array.stepBy`)
    end
    end

    return stepBy end function __DARKLUA_BUNDLE_MODULES.aj():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aj if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aj=v end return v.c end end do local function __modImpl()

    local function sum(array:{number},initialValue:number?):number
    local result=if initialValue==nil then 0 else initialValue

    for _,element in array do
    result+=element
    end

    return result
    end

    return sum end function __DARKLUA_BUNDLE_MODULES.ak():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ak if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ak=v end return v.c end end do local function __modImpl()

    local function sumBy<T>(array:{T},map:(T)->number,initialValue:number?):number
    local result=if initialValue==nil then 0 else initialValue

    for _,element in array do
    result+=map(element)
    end

    return result
    end

    return sumBy end function __DARKLUA_BUNDLE_MODULES.al():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.al if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.al=v end return v.c end end do local function __modImpl()

    local function takeWhile<T>(
    array:{T},
    predicate:(element:T,index:number)->boolean,
    start:number?
    ):{T}
    local arrayLength=#array

    if arrayLength==0 then
    return array
    end

    local bound=arrayLength+1
    local actualStart=if start==nil then 1 else start
    if actualStart==1 then
    for index,element in array do
    if not predicate(element,index)then
    bound=index
    break
    end
    end
    else
    local length=#array
    for i=actualStart,length do
    local element=array[i]
    if not predicate(element,i)then
    bound=i
    break
    end
    end
    end

    if actualStart==bound then
    return{}
    elseif actualStart==1 and bound>arrayLength then
    return array
    end

    local toInsert=bound-actualStart

    if actualStart==1 and toInsert<arrayLength/2 then
    local result=table.clone(array)

    for _=1,arrayLength-bound do
    table.remove(result)
    end

    return result
    else
    local result={}

    for i=actualStart,bound-1 do
    table.insert(result,array[i])
    end

    return result
    end
    end

    return takeWhile end function __DARKLUA_BUNDLE_MODULES.am():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.am if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.am=v end return v.c end end do local function __modImpl()

    local reduce=__DARKLUA_BUNDLE_MODULES.c()

    local function zip<T>(array:{T},...:{T}):{{T}}
    local alternateWith={...}

    local minimumLength=reduce(alternateWith,function(minimum:number,value)
    return math.min(minimum,#value)
    end,#array)

    if minimumLength==0 then
    return{}
    end

    local result={}

    for i=1,minimumLength do
    local entry={array[i]}
    for _,otherArray in alternateWith do
    table.insert(entry,otherArray[i])
    end
    table.insert(result,entry)
    end

    return result
    end






    return(zip::any)::zip1__DARKLUA_TYPE_j&zip2__DARKLUA_TYPE_k&zip3__DARKLUA_TYPE_l&zipAll__DARKLUA_TYPE_m end function __DARKLUA_BUNDLE_MODULES.an():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.an if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.an=v end return v.c end end do local function __modImpl()

    return table.clone end function __DARKLUA_BUNDLE_MODULES.ao():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ao if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ao=v end return v.c end end do local function __modImpl()

    local function count<K,V>(map:{[K]:V}):number
    local length=0
    for _ in map do
    length+=1
    end
    return length
    end

    return count end function __DARKLUA_BUNDLE_MODULES.ap():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ap if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ap=v end return v.c end end do local function __modImpl()

    local function entries<K,V>(map:{[K]:V},keyIndex:any?,valueIndex:any?):{{[any]:K|V}}
    local useKeyIndex=if keyIndex==nil then 1 else keyIndex
    local useValueIndex=if valueIndex==nil then useKeyIndex+1 else valueIndex

    local array={}

    for key,value in map do
    table.insert(array,{
    [useKeyIndex]=key::K|V,
    [useValueIndex]=value,
    })
    end

    return array
    end





    return entries::EntriesFn__DARKLUA_TYPE_n end function __DARKLUA_BUNDLE_MODULES.aq():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aq if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aq=v end return v.c end end do local function __modImpl()

    local function fromEntries<K,V>(
    entries:{{[any]:K|V}},
    keyIndex:any?,
    valueIndex:any?
    ):{[K]:V}
    local useKeyIndex=if keyIndex==nil then 1 else keyIndex
    local useValueIndex=if valueIndex==nil then useKeyIndex+1 else valueIndex

    local result={}::{[K]:V}

    for _,entry in entries do
    local key=entry[useKeyIndex]::K
    local value=entry[useValueIndex]::V
    result[key]=value
    end

    return result
    end





    return fromEntries::FromEntriesFn__DARKLUA_TYPE_o end function __DARKLUA_BUNDLE_MODULES.ar():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ar if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ar=v end return v.c end end do local function __modImpl()

    local function invert<K,V>(map:{[K]:V}):{[V]:K}
    if next(map)==nil then
    return map::any
    end

    local result={}
    for key,value in map do
    result[value]=key
    end
    return result
    end

    return invert end function __DARKLUA_BUNDLE_MODULES.as():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.as if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.as=v end return v.c end end do local function __modImpl()

    local function isEmpty(value:{[any]:any}):boolean
    return next(value)==nil
    end

    return isEmpty end function __DARKLUA_BUNDLE_MODULES.at():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.at if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.at=v end return v.c end end do local function __modImpl()

    local function keys<K,V>(map:{[K]:V}):{K}
    local result={}
    for key in map do
    table.insert(result,key)
    end
    return result
    end

    return keys end function __DARKLUA_BUNDLE_MODULES.au():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.au if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.au=v end return v.c end end do local function __modImpl()

    local function mapEntries<K,V,K2,V2>(map:{[K]:V},mapFn:(key:K,value:V)->(K2?,V2?)):{[K2]:V2}
    local result={}

    for key,value in map do
    local newKey,newValue=mapFn(key,value)
    if newKey~=nil and newValue~=nil then
    result[newKey]=newValue
    end
    end

    return result
    end

    return mapEntries end function __DARKLUA_BUNDLE_MODULES.av():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.av if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.av=v end return v.c end end do local function __modImpl()

    local None=table.freeze(setmetatable({},{
    __index=function()
    error('attempt to index on None symbol')
    end,
    __tostring=function()
    return'<None>'
    end,
    }))

    return None end function __DARKLUA_BUNDLE_MODULES.aw():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aw if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aw=v end return v.c end end do local function __modImpl()

    local None=__DARKLUA_BUNDLE_MODULES.aw()

    local function mapValues<K,V,W>(map:{[K]:V},mapFn:(value:V,key:K)->W?):{[K]:W}
    local result={}

    for key,value in map do
    local newValue=mapFn(value,key)
    if newValue~=nil and newValue~=(None::any)then
    result[key]=newValue
    end
    end

    return result
    end

    return mapValues end function __DARKLUA_BUNDLE_MODULES.ax():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ax if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ax=v end return v.c end end do local function __modImpl()

    local None=__DARKLUA_BUNDLE_MODULES.aw()

    local function merge<T,U...>(...:U...):any
    local first
    local firstIndex
    local length=select('#',...)

    for i=1,length do
    local mergeMap=select(i,...)

    if mergeMap~=nil then
    firstIndex=i
    first=mergeMap
    break
    end
    end

    if first==nil then
    error('attempt to merge only nil values')
    end

    if firstIndex==length then
    return first
    end

    local result

    for i=firstIndex+1,length do
    local mergeMap=select(i,...)

    if mergeMap~=nil then
    if result==nil then
    result=table.clone(first)
    setmetatable(result,nil)
    end

    local metatable=getmetatable(mergeMap)

    if metatable~=nil and type(metatable.__call)=='function'then
    for key,value in pairs(mergeMap)do
    if value==None then
    result[key]=nil
    else
    result[key]=value
    end
    end
    else
    for key,value in mergeMap do
    if value==None then
    result[key]=nil
    else
    result[key]=value
    end
    end
    end
    end
    end

    return result or first
    end








    return(merge::any)::merge1__DARKLUA_TYPE_p&merge2__DARKLUA_TYPE_q&merge3__DARKLUA_TYPE_r&merge4__DARKLUA_TYPE_s&merge5__DARKLUA_TYPE_t&mergeAll__DARKLUA_TYPE_u end function __DARKLUA_BUNDLE_MODULES.ay():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.ay if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.ay=v end return v.c end end do local function __modImpl()

    local isEmpty=__DARKLUA_BUNDLE_MODULES.at()

    local function remove<K,V>(map:{[K]:V},...:K?)
    local removeLength=select('#',...)

    if removeLength==0 or isEmpty(map)then
    return map
    else
    local result

    for i=1,removeLength do
    local key:K=select(i,...)

    if key~=nil and map[key]~=nil then
    result=result or table.clone(map)
    result[key]=nil
    end
    end

    return result or map
    end
    end

    return remove end function __DARKLUA_BUNDLE_MODULES.az():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.az if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.az=v end return v.c end end do local function __modImpl()

    local function values<K,V>(map:{[K]:V}):{V}
    local result={}
    for _,value in map do
    table.insert(result,value)
    end
    return result
    end

    return values end function __DARKLUA_BUNDLE_MODULES.aA():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aA if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aA=v end return v.c end end do local function __modImpl()

    local function count(set:{[any]:any}):number
    local length=0
    for _ in set do
    length+=1
    end
    return length
    end

    return count end function __DARKLUA_BUNDLE_MODULES.aB():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aB if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aB=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()



    local function filter<T>(set:Set__DARKLUA_TYPE_v<T>,predicate:(value:T)->boolean):Set__DARKLUA_TYPE_v<T>
    local result:Set__DARKLUA_TYPE_v<T> ={}

    for value in set do
    if predicate(value)then
    result[value]=true
    end
    end

    return result
    end

    return filter end function __DARKLUA_BUNDLE_MODULES.aC():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aC if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aC=v end return v.c end end do local function __modImpl()

    local type=__DARKLUA_BUNDLE_MODULES.a()



    local function fromArray<T>(array:{T}):Set__DARKLUA_TYPE_w<T>
    local set:Set__DARKLUA_TYPE_w<T> ={}
    for _,element in array do
    set[element]=true
    end
    return set
    end

    return fromArray end function __DARKLUA_BUNDLE_MODULES.aD():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aD if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aD=v end return v.c end end do local function __modImpl()

    local type=__DARKLUA_BUNDLE_MODULES.a()



    local function fromFn<T>(generator:(number)->T?):Set__DARKLUA_TYPE_x<T>
    local set:Set__DARKLUA_TYPE_x<T> ={}

    local i=1
    while true do
    local element=generator(i)
    i+=1
    if element==nil then
    break
    elseif set[element]==nil then
    set[element]=true
    end
    end

    return set
    end

    return fromFn end function __DARKLUA_BUNDLE_MODULES.aE():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aE if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aE=v end return v.c end end do local function __modImpl()

    local type=__DARKLUA_BUNDLE_MODULES.a()



    local function fromTryFn<T>(generator:(number)->T?):Set__DARKLUA_TYPE_y<T>
    local set:Set__DARKLUA_TYPE_y<T> ={}

    local i=1
    while true do
    local success,element=pcall(generator,i)
    i+=1
    if success==false or element==nil then
    break
    elseif set[element]==nil then
    set[element]=true
    end
    end

    return set
    end

    return fromTryFn end function __DARKLUA_BUNDLE_MODULES.aF():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aF if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aF=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()



    local function intersect<T>(...:Set__DARKLUA_TYPE_z<T>?):Set__DARKLUA_TYPE_z<T>
    local sets={}

    for i=1,select('#',...)do
    local setValue=select(i,...)
    if setValue then
    if next(setValue)==nil then
    return{}
    end

    table.insert(sets,setValue)
    end
    end

    local length=#sets

    if length==0 then
    return{}
    elseif length==1 then
    return sets[1]
    else
    local removeKeys={}
    local first=sets[1]

    for key in first do
    for i=2,length do
    local currentSet=sets[i]

    if not currentSet[key]then
    table.insert(removeKeys,key)
    break
    end
    end
    end

    if#removeKeys==0 then
    return first
    end

    local result:Set__DARKLUA_TYPE_z<T> =table.clone(first)

    for _,key in removeKeys do
    result[key]=nil
    end

    return result
    end
    end

    return intersect end function __DARKLUA_BUNDLE_MODULES.aG():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aG if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aG=v end return v.c end end do local function __modImpl()

    local function isEmpty(value:{[any]:any}):boolean
    return next(value)==nil
    end

    return isEmpty end function __DARKLUA_BUNDLE_MODULES.aH():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aH if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aH=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()



    local function map<T,U>(set:Set__DARKLUA_TYPE_A<T>,fn:(value:T)->U?):Set__DARKLUA_TYPE_A<U>
    local result:Set__DARKLUA_TYPE_A<U> ={}

    for value in set do
    local entry=fn(value)
    if entry~=nil then
    result[entry]=true
    end
    end

    return result::Set__DARKLUA_TYPE_A<U>
    end

    return map end function __DARKLUA_BUNDLE_MODULES.aI():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aI if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aI=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()



    local function merge<T>(...:Set__DARKLUA_TYPE_B<T>?):Set__DARKLUA_TYPE_B<T>
    local first
    local firstIndex
    local length=select('#',...)

    for i=1,length do
    local mergeSet=select(i,...)

    if mergeSet~=nil then
    firstIndex=i
    first=mergeSet
    break
    end
    end

    if first==nil then
    error('attempt to merge only nil values')
    end

    if firstIndex==length then
    return first
    end

    local result

    for i=firstIndex+1,length do
    local mergeSet=select(i,...)

    if mergeSet~=nil then
    if result==nil then
    result=table.clone(first)
    setmetatable(result,nil)
    end

    local metatable=getmetatable(mergeSet)

    if metatable~=nil and type(metatable.__call)=='function'then
    for key in pairs(mergeSet)do
    result[key]=true
    end
    else
    for key in mergeSet do
    result[key]=true
    end
    end
    end
    end

    return result or first
    end

    return merge end function __DARKLUA_BUNDLE_MODULES.aJ():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aJ if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aJ=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()
    local isEmpty=__DARKLUA_BUNDLE_MODULES.aH()



    local function removeValues<T>(set:Set__DARKLUA_TYPE_C<T>,...:T?):Set__DARKLUA_TYPE_C<T>
    local removeLength=select('#',...)

    if removeLength==0 or isEmpty(set)then
    return set
    end

    local result

    for i=1,removeLength do
    local value:T?=select(i,...)

    if value~=nil and set[value]~=nil then
    if result==nil then
    result=table.clone(set)
    end
    result[value]=nil
    end
    end

    return result or set
    end

    return removeValues end function __DARKLUA_BUNDLE_MODULES.aK():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aK if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aK=v end return v.c end end do local function __modImpl()

    local SetType=__DARKLUA_BUNDLE_MODULES.a()



    local function toArray<T>(set:Set__DARKLUA_TYPE_D<T>):{T}
    local result={}
    for value in set do
    table.insert(result,value)
    end
    return result
    end

    return toArray end function __DARKLUA_BUNDLE_MODULES.aL():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aL if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aL=v end return v.c end end do local function __modImpl()

    local WEAK_KEYS_METATABLE={__mode='k'}

    local function WeakMap<K,V>(default:{[K]:V}?):{[K]:V}
    local value=default or{}
    return setmetatable(value::any,WEAK_KEYS_METATABLE)::any
    end

    return WeakMap end function __DARKLUA_BUNDLE_MODULES.aM():typeof(__modImpl())local v=__DARKLUA_BUNDLE_MODULES.cache.aM if not v then v={c=__modImpl()}__DARKLUA_BUNDLE_MODULES.cache.aM=v end return v.c end end end

    local setType=__DARKLUA_BUNDLE_MODULES.a()

    export type Set<T> =Set__DARKLUA_TYPE_a<T>

    local Disk={
    Array={
    all=__DARKLUA_BUNDLE_MODULES.b(),
    alternate=__DARKLUA_BUNDLE_MODULES.d(),
    any=__DARKLUA_BUNDLE_MODULES.e(),
    average=__DARKLUA_BUNDLE_MODULES.f(),
    averageBy=__DARKLUA_BUNDLE_MODULES.g(),
    binarySearch=__DARKLUA_BUNDLE_MODULES.h(),
    binarySearchByKey=__DARKLUA_BUNDLE_MODULES.i(),
    chunks=__DARKLUA_BUNDLE_MODULES.j(),
    concat=__DARKLUA_BUNDLE_MODULES.k(),
    contains=__DARKLUA_BUNDLE_MODULES.l(),
    copy=__DARKLUA_BUNDLE_MODULES.m(),
    count=__DARKLUA_BUNDLE_MODULES.n(),
    deduplicate=__DARKLUA_BUNDLE_MODULES.o(),
    deduplicateByKey=__DARKLUA_BUNDLE_MODULES.p(),
    difference=__DARKLUA_BUNDLE_MODULES.r(),
    differenceSymmetric=__DARKLUA_BUNDLE_MODULES.s(),
    filter=__DARKLUA_BUNDLE_MODULES.t(),
    find=__DARKLUA_BUNDLE_MODULES.u(),
    findClosest=__DARKLUA_BUNDLE_MODULES.v(),
    findClosestBy=__DARKLUA_BUNDLE_MODULES.w(),
    findClosestIndex=__DARKLUA_BUNDLE_MODULES.x(),
    findClosestIndexBy=__DARKLUA_BUNDLE_MODULES.y(),
    findIndex=__DARKLUA_BUNDLE_MODULES.z(),
    findIndexByValue=__DARKLUA_BUNDLE_MODULES.A(),
    findMap=__DARKLUA_BUNDLE_MODULES.B(),
    flatMap=__DARKLUA_BUNDLE_MODULES.D(),
    flatten=__DARKLUA_BUNDLE_MODULES.E(),
    fromFn=__DARKLUA_BUNDLE_MODULES.F(),
    fromTryFn=__DARKLUA_BUNDLE_MODULES.G(),
    insertAfter=__DARKLUA_BUNDLE_MODULES.H(),
    insertAfterIndex=__DARKLUA_BUNDLE_MODULES.I(),
    insertBefore=__DARKLUA_BUNDLE_MODULES.J(),
    insertBeforeIndex=__DARKLUA_BUNDLE_MODULES.K(),
    isArray=__DARKLUA_BUNDLE_MODULES.C(),
    isEmpty=__DARKLUA_BUNDLE_MODULES.L(),
    map=__DARKLUA_BUNDLE_MODULES.M(),
    maximum=__DARKLUA_BUNDLE_MODULES.N(),
    maximumBy=__DARKLUA_BUNDLE_MODULES.O(),
    minimum=__DARKLUA_BUNDLE_MODULES.P(),
    minimumBy=__DARKLUA_BUNDLE_MODULES.Q(),
    partition=__DARKLUA_BUNDLE_MODULES.R(),
    pluck=__DARKLUA_BUNDLE_MODULES.S(),
    pop=__DARKLUA_BUNDLE_MODULES.T(),
    popFirst=__DARKLUA_BUNDLE_MODULES.U(),
    product=__DARKLUA_BUNDLE_MODULES.V(),
    productBy=__DARKLUA_BUNDLE_MODULES.W(),
    push=__DARKLUA_BUNDLE_MODULES.X(),
    range=__DARKLUA_BUNDLE_MODULES.Y(),
    reduce=__DARKLUA_BUNDLE_MODULES.c(),
    removeIndexes=__DARKLUA_BUNDLE_MODULES._(),
    removeSortedIndexes=__DARKLUA_BUNDLE_MODULES.q(),
    removeValues=__DARKLUA_BUNDLE_MODULES.aa(),
    repeatSequence=__DARKLUA_BUNDLE_MODULES.ab(),
    replaceAtIndex=__DARKLUA_BUNDLE_MODULES.ac(),
    reverse=__DARKLUA_BUNDLE_MODULES.ad(),
    reversed=__DARKLUA_BUNDLE_MODULES.ad(),
    reverseFind=__DARKLUA_BUNDLE_MODULES.ae(),
    reverseFindIndex=__DARKLUA_BUNDLE_MODULES.af(),
    reverseFindIndexByValue=__DARKLUA_BUNDLE_MODULES.ag(),
    reverseFindMap=__DARKLUA_BUNDLE_MODULES.ah(),
    sort=__DARKLUA_BUNDLE_MODULES.Z(),
    sortByKey=__DARKLUA_BUNDLE_MODULES.ai(),
    stepBy=__DARKLUA_BUNDLE_MODULES.aj(),
    sum=__DARKLUA_BUNDLE_MODULES.ak(),
    sumBy=__DARKLUA_BUNDLE_MODULES.al(),
    takeWhile=__DARKLUA_BUNDLE_MODULES.am(),
    zip=__DARKLUA_BUNDLE_MODULES.an(),
    },
    Map={
    copy=__DARKLUA_BUNDLE_MODULES.ao(),
    count=__DARKLUA_BUNDLE_MODULES.ap(),
    entries=__DARKLUA_BUNDLE_MODULES.aq(),
    fromEntries=__DARKLUA_BUNDLE_MODULES.ar(),
    invert=__DARKLUA_BUNDLE_MODULES.as(),
    isEmpty=__DARKLUA_BUNDLE_MODULES.at(),
    keys=__DARKLUA_BUNDLE_MODULES.au(),
    mapEntries=__DARKLUA_BUNDLE_MODULES.av(),
    mapValues=__DARKLUA_BUNDLE_MODULES.ax(),
    merge=__DARKLUA_BUNDLE_MODULES.ay(),
    remove=__DARKLUA_BUNDLE_MODULES.az(),
    values=__DARKLUA_BUNDLE_MODULES.aA(),
    },
    Set={
    count=__DARKLUA_BUNDLE_MODULES.aB(),
    filter=__DARKLUA_BUNDLE_MODULES.aC(),
    fromArray=__DARKLUA_BUNDLE_MODULES.aD(),
    fromFn=__DARKLUA_BUNDLE_MODULES.aE(),
    fromTryFn=__DARKLUA_BUNDLE_MODULES.aF(),
    intersect=__DARKLUA_BUNDLE_MODULES.aG(),
    isEmpty=__DARKLUA_BUNDLE_MODULES.aH(),
    map=__DARKLUA_BUNDLE_MODULES.aI(),
    merge=__DARKLUA_BUNDLE_MODULES.aJ(),
    removeValues=__DARKLUA_BUNDLE_MODULES.aK(),
    toArray=__DARKLUA_BUNDLE_MODULES.aL(),
    },
    None=__DARKLUA_BUNDLE_MODULES.aw(),
    WeakMap=__DARKLUA_BUNDLE_MODULES.aM(),
    }

    return Disk
end)()

-- Compares arrays, maps, and sets without depending on iteration order.
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

-- Asserts that two Disk values have the same contents.
local function assertSame(actual, expected)
    assert(same(actual, expected), "values differ")
end

-- Runs one named Disk assertion group.
local function check(name, test)
    local ok, err = pcall(test)
    assert(ok, name .. ": " .. tostring(err))
end

-- Checks that an operation rejects its input.
local function rejects(name, operation)
    check(name, function()
        local ok = pcall(operation)
        assert(not ok, "operation unexpectedly succeeded")
    end)
end

-- Returns a sorted copy for APIs whose result is a map-backed collection.
local function sorted(values)
    local result = table.clone(values)
    table.sort(result, function(left, right)
        return tostring(left) < tostring(right)
    end)
    return result
end

local A = Disk.Array
local M = Disk.Map
local S = Disk.Set

check("array predicates and arithmetic", function()
    assert(A.all({}, function() return false end))
    assert(A.all({ 1, 2, 3 }, function(value) return value < 4 end))
    assert(not A.all({ 1, 2, 5 }, function(value) return value < 4 end))
    assert(A.any({ 1, 2, 3 }, function(value) return value == 2 end))
    assert(not A.any({ 1, 3 }, function(value) return value == 2 end))
    assert(A.average({ 2, 4, 6 }) == 4)
    assert(A.average({}) == nil)
    assert(A.averageBy({ "a", "bb", "ccc" }, function(value) return #value end) == 2)
    assert(A.sum({ 1, 2, 3 }) == 6)
    assert(A.sum({ 1, 2, 3 }, 10) == 16)
    assert(A.sumBy({ "a", "bb" }, function(value) return #value end) == 3)
    assert(A.product({ 2, 3, 4 }) == 24)
    assert(A.productBy({ 2, 3 }, function(value) return value + 1 end) == 12)
    assert(A.maximum({ 1, 8, 3 }) == 8)
    assert(A.minimum({ 1, 8, 3 }) == 1)
    assert(A.maximumBy({ "a", "bbb", "cc" }, function(value) return #value end) == 3)
    assert(A.minimumBy({ "a", "bbb", "cc" }, function(value) return #value end) == 1)
end)

check("array search", function()
    assert(A.binarySearch({ 1, 3, 5, 7 }, 5) == 3)
    assert(A.binarySearch({ 1, 3, 5, 7 }, 4) == nil)
    assert(A.binarySearchByKey({ { id = 1 }, { id = 4 }, { id = 9 } }, 4, function(value) return value.id end) == 2)
    assert(A.contains({ "a", "b" }, "b"))
    assert(not A.contains({ "a", "b" }, "c"))
    assert(A.find({ "a", "b", "c" }, function(value) return value == "b" end) == "b")
    assert(A.findIndex({ "a", "b", "c" }, function(value) return value == "b" end) == 2)
    assert(A.findIndexByValue({ "a", "b", "c" }, "c") == 3)
    assert(A.findClosest({ 10, 20, 30 }, 23) == 20)
    assert(A.findClosestIndex({ 10, 20, 30 }, 23) == 2)
    assert(A.findClosestBy({ 10, 20, 30 }, function(value) return math.abs(value - 23) end) == 20)
    assert(A.findClosestIndexBy({ 10, 20, 30 }, function(value) return math.abs(value - 23) end) == 2)
    assert(A.findMap({ 1, 2, 3 }, function(value) if value == 2 then return value * 10 end end) == 20)
    assert(A.reverseFind({ 1, 2, 3, 2 }, function(value) return value == 2 end) == 2)
    assert(A.reverseFindIndex({ 1, 2, 3, 2 }, function(value) return value == 2 end) == 4)
    assert(A.reverseFindIndexByValue({ 1, 2, 3, 2 }, 2) == 4)
    assert(A.reverseFindMap({ 1, 2, 3 }, function(value) if value == 2 then return 20 end end) == 20)
end)

check("array transformations", function()
    assertSame(A.alternate({ 2, 4 }, { 3, 5 }), { 2, 3, 4, 5 })
    assertSame(A.alternate({ 2, 4 }, { "a", "b" }, { 3, 5 }), { 2, "a", 3, 4, "b", 5 })
    assertSame(A.zip({ 1, 2 }, { "a", "b" }), { { 1, "a" }, { 2, "b" } })
    assertSame(A.chunks({ 1, 2, 3, 4, 5 }, 2), { { 1, 2 }, { 3, 4 }, { 5 } })
    assertSame(A.concat({ 1, 2 }, { 3 }, { 4, 5 }), { 1, 2, 3, 4, 5 })
    assertSame(A.deduplicate({ 1, 2, 1, 3, 2 }), { 1, 2, 3 })
    assertSame(A.deduplicateByKey({ { id = 1 }, { id = 2 }, { id = 1 } }, function(value) return value.id end), { { id = 1 }, { id = 2 } })
    assertSame(A.difference({ 1, 2, 3 }, { 2, 4 }), { 1, 3 })
    assertSame(A.differenceSymmetric({ 1, 2, 3 }, { 2, 3, 4 }), { 1, 4 })
    assertSame(A.filter({ 1, 2, 3, 4 }, function(value) return value % 2 == 0 end), { 2, 4 })
    assertSame(A.flatMap({ 1, 2, 3 }, function(value) return { value, value * 10 } end), { 1, 10, 2, 20, 3, 30 })
    assertSame(A.flatten({ 1, { 2, { 3, 4 } }, 5 }), { 1, 2, 3, 4, 5 })
    assertSame(A.flatten({ 1, { 2, { 3, 4 } }, 5 }, 1), { 1, 2, { 3, 4 }, 5 })
    assertSame(A.fromFn(function(index) if index <= 3 then return index * 2 end end), { 2, 4, 6 })
    assertSame(A.fromTryFn(function(index) if index == 3 then error("stop") end return index end), { 1, 2 })
    assertSame(A.insertAfter({ 1, 2, 3 }, 9, function(value) return value == 2 end), { 1, 2, 9, 3 })
    assertSame(A.insertAfterIndex({ 1, 2, 3 }, 9, 2), { 1, 2, 9, 3 })
    assertSame(A.insertBefore({ 1, 2, 3 }, 9, function(value) return value == 2 end), { 1, 9, 2, 3 })
    assertSame(A.insertBeforeIndex({ 1, 2, 3 }, 9, 2), { 1, 9, 2, 3 })
    assert(A.isArray({}) and A.isArray({ 1, 2, 3 }))
    assert(not A.isArray({ [2] = true }))
    assert(A.isEmpty({}))
    assert(not A.isEmpty({ 1 }))
    assertSame(A.map({ 1, 2, 3 }, function(value) if value == 2 then return nil end return value * 2 end), { 2, 6 })
    local objects = { { name = "z" }, { name = "a" }, { name = "m" } }
    assertSame(A.sortByKey(objects, function(value) return value.name end), { { name = "a" }, { name = "m" }, { name = "z" } })
    local evens, odds = A.partition({ 1, 2, 3, 4 }, function(value) return value % 2 == 0 end)
    assertSame(evens, { 2, 4 })
    assertSame(odds, { 1, 3 })
end)

check("array slicing and removal", function()
    assertSame(A.pop({ 1, 2, 3 }), { 1, 2 })
    assertSame(A.pop({ 1, 2, 3 }, 2), { 1 })
    assertSame(A.popFirst({ 1, 2, 3 }), { 2, 3 })
    assertSame(A.popFirst({ 1, 2, 3 }, 2), { 3 })
    assertSame(A.push({ 1, 2 }, 3, 4), { 1, 2, 3, 4 })
    assertSame(A.range({ "a", "b", "c", "d" }, 2, 3), { "b", "c" })
    assertSame(A.range({ "a", "b", "c", "d" }, 3, 2), { "c", "b" })
    assertSame(A.range({ "a", "b", "c", "d" }, -1, 1), { "d", "c", "b", "a" })
    assertSame(A.removeIndexes({ "a", "b", "c", "d" }, { 2, 4 }), { "a", "c" })
    assertSame(A.removeSortedIndexes({ "a", "b", "c", "d" }, { 2, 4 }), { "a", "c" })
    assertSame(A.removeValues({ 1, 2, 3, 2 }, 2), { 1, 3 })
    assertSame(A.repeatSequence({ 1, 2 }, 3), { 1, 2, 1, 2, 1, 2 })
    assertSame(A.replaceAtIndex({ 1, 2, 3 }, 2, 9), { 1, 9, 3 })
    assertSame(A.reverse({ 1, 2, 3 }), { 3, 2, 1 })
    assertSame(A.reversed({ 1, 2, 3 }), { 3, 2, 1 })
    assertSame(A.stepBy({ 1, 2, 3, 4, 5 }, 2), { 1, 3, 5 })
    assertSame(A.stepBy({ 1, 2, 3, 4, 5 }, -2), { 5, 3, 1 })
    assertSame(A.takeWhile({ 1, 2, 4, 3 }, function(value) return value < 4 end), { 1, 2 })
    rejects("zero step", function() A.stepBy({ 1, 2 }, 0) end)
end)

check("array identity and immutability", function()
    local original = { 1, 2, 3 }
    local copied = A.copy(original)
    assert(copied ~= original)
    assertSame(copied, original)
    assert(A.concat(original) == original)
    local empty = {}
    assert(A.range(empty, 1, 3) == empty)
    local single = { 1 }
    assert(A.reverse(single) == single)
end)

check("map operations", function()
    local map = { a = 1, b = 2, c = 3 }
    assert(M.count(map) == 3)
    assert(M.isEmpty({}))
    assert(not M.isEmpty(map))
    assertSame(M.copy(map), map)
    assertSame(sorted(M.keys(map)), { "a", "b", "c" })
    assertSame(sorted(M.values(map)), { 1, 2, 3 })
    assertSame(M.invert({ a = "x", b = "y" }), { x = "a", y = "b" })
    assertSame(M.fromEntries({ { "a", 1 }, { "b", 2 }, { "a", 3 } }), { a = 3, b = 2 })
    assertSame(M.mapValues(map, function(value) if value == 2 then return nil end return value * 10 end), { a = 10, c = 30 })
    assertSame(M.mapEntries(map, function(key, value) return key:upper(), value end), { A = 1, B = 2, C = 3 })
    assertSame(M.merge({ a = 1, b = 2 }, { b = 3, c = 4 }), { a = 1, b = 3, c = 4 })
    assertSame(M.remove({ a = 1, b = 2 }, "a"), { b = 2 })

    local entries = M.entries(map)
    table.sort(entries, function(left, right) return left[1] < right[1] end)
    assertSame(entries, { { "a", 1 }, { "b", 2 }, { "c", 3 } })

    local keyed_entries = M.entries({ a = 1, b = 2 }, "key", "value")
    table.sort(keyed_entries, function(left, right) return left.key < right.key end)
    assertSame(keyed_entries, { { key = "a", value = 1 }, { key = "b", value = 2 } })

    assertSame(M.mapValues({ a = 1, b = 2 }, function(value) if value == 1 then return Disk.None end return value end), { b = 2 })
end)

check("set operations", function()
    local first = S.fromArray({ 1, 2, 2, 3 })
    local second = S.fromArray({ 3, 4, 5 })
    assertSame(first, { [1] = true, [2] = true, [3] = true })
    assert(S.count(first) == 3)
    assert(S.isEmpty(S.fromArray({})))
    assertSame(S.filter(first, function(value) return value > 1 end), { [2] = true, [3] = true })
    assertSame(S.intersect(first, second), { [3] = true })
    assertSame(S.merge(first, second), { [1] = true, [2] = true, [3] = true, [4] = true, [5] = true })
    assertSame(S.removeValues(first, 2), { [1] = true, [3] = true })
    assertSame(S.map(first, function(value) return value * 10 end), { [10] = true, [20] = true, [30] = true })
    assertSame(S.map(first, function(value) if value == 2 then return nil end return value end), { [1] = true, [3] = true })

    local generated = S.fromFn(function(index) if index <= 3 then return index end end)
    assertSame(generated, { [1] = true, [2] = true, [3] = true })
    local tried = S.fromTryFn(function(index) if index == 3 then error("stop") end return index end)
    assertSame(tried, { [1] = true, [2] = true })

    local values = sorted(S.toArray(first))
    assertSame(values, { 1, 2, 3 })
    assertSame(S.intersect(), {})
end)

check("sentinel and weak map", function()
    assert(Disk.None ~= nil)
    local weak = Disk.WeakMap({})
    local metatable = getmetatable(weak)
    assert(metatable and metatable.__mode == "k")
    local key = {}
    weak[key] = "value"
    assert(weak[key] == "value")
end)

print("disk: ok")
