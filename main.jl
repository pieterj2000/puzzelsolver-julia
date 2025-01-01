using Images, FileIO, ImageTransformations
using Base.Threads
using Statistics
using FTPClient
using ImageMorphology
using Graphs
using Plots
using Dierckx
using Serialization
using TranscodingStreams
using CodecZstd
#using Mux, WebIO, Interact

## Get image
function getNewestImage()
    ftp = FTP("ftp://pieter:ww@192.168.2.7:2211/DCIM/Camera")
    files = readdir(ftp)
    filename = last(filter(startswith("PXL_"), files))
    file = download(ftp,filename)
    close(ftp)
    img = load(file)
    return img
end

function getIPImage(address)
    img = load(address)
    return img
end

## STRUCTS
struct Bounds
    ytop :: Int64
    ybottom :: Int64
    xleft :: Int64
    xright :: Int64
end

struct Segment
    curve :: ParametricSpline
    kant :: Int
    buiten :: Bool
    corners :: Tuple{Vector{Float64}, Vector{Float64}}
    cornerspixel :: Tuple{CartesianIndex{2},CartesianIndex{2}} 
    # todo colors
end

struct Stukje
    randen :: Tuple{Segment, Segment, Segment, Segment}
    rawimg :: Matrix{RGB{N0f8}}
    rawimgbounds :: Bounds
    maskparams :: NTuple{4, Float64}
end


##### FUNCTIONS FOR PROCESSING IMAGE
function getmask(img, params)
    (sm, vm, c, e) = params
    mask = zeros(size(img))

    hsv_img = HSV.(img)
    channels = channelview(float.(hsv_img))
    saturation = channels[2,:,:]
    value = channels[3,:,:]
    saturation[value .<0.1] .= 0

    mask[saturation*sm+value*vm .- c .> e] .= 1
    step1 = imfill(Bool.(mask), 0:10000)
    step2 = .!(step1)
    mask = .!(imfill(step2, 0:10000))
    return mask
end

function refinemask(img, params)
    (sm, vm, c, e) = params
    mask = zeros(size(img))

    hsv_img = HSV.(img)
    channels = channelview(float.(hsv_img))
    saturation = channels[2,:,:]
    value = channels[3,:,:]
    saturation[value .<0.1] .= 0

    mask[saturation*sm+value*vm .- c .> e] .= 1
    step1 = imfill(Bool.(mask), 0:10000)
    step2 = .!(step1)
    mask = .!(imfill(step2, 0:10000))

    display(Gray.(saturation))
    display(Gray.(value))
    display(Gray.(saturation*sm+value*vm .- c))
    display(Gray.(mask))
end

function makeborder(mask)
    return border = dilate(.!(mask)) .& mask
end

function toCartesian(img, index)
    width = size(img)[1]
    return CartesianIndex(mod(index-1, width)+1, div(index-1, width)+1)
end

function thinborder(border)
    edges = [ (p.first, qx ) 
                for p=pairs(border), diff=[CartesianIndex(0,1), CartesianIndex(1,0)] 
                for qx=[p.first + diff] 
                if p.second == 1 && border[qx] == 1]
    linearindices = LinearIndices(border)
    edgeslinind = map( tup -> Edge(linearindices[tup[1]], linearindices[tup[2]]), edges)

    g = SimpleGraphFromIterator(edgeslinind)
    v = first(filter( v -> degree(g,v) == 2, vertices(g)))
    n = neighbors(g,v)[1]
    rem_edge!(g,Edge(v,n))

    shortestpath = a_star(g, v, n)
    cycle = map(src, shortestpath)
    push!(cycle, n)

    cyclecoord = map(x -> toCartesian(border,x), cycle)
    bordernew = zeros(size(border))
    bordernew[cyclecoord] .= 1
    return (cyclecoord,bordernew)
end

function thinborderupdatemask(border, mask)
    (bordercoords, tborder) = thinborder(border)
    mask = mask .- (border .- tborder)
    return (bordercoords, tborder, mask)
end

function getcorners(
            bordercoords :: Vector{CartesianIndex{2}},
            border,
            mask
        ) :: NTuple{4, CartesianIndex{2}}
    tmpmask = Gray.(copy(mask))
    kr = 5 # 30
    krm = 5 # 1
    @threads for c in bordercoords
        som = 0
        i = 0
        for dc = [ CartesianIndex(krm*dx,krm*dy) for dx=-kr:kr, dy=-kr:kr ]
            som += mask[c+dc]
            i += 1
        end
        avg = som/i
        tmpmask[c] = avg
    end

    bordercopy = copy(bordercoords)

    corners = Vector{CartesianIndex{2}}(undef, 4)
    
    for i in 1:4
        m = partialsort(bordercopy, by=(c -> tmpmask[c]), 1)
        corners[i] = m
        m = Tuple(m)
        filter!(c -> abs(Tuple(c)[1] - m[1]) + abs(Tuple(c)[2] - m[2]) > 500, bordercopy)
    end

    tl = argmin(c -> Tuple(c)[1] + Tuple(c)[2], corners)
    bl = argmin(c -> -Tuple(c)[1] + Tuple(c)[2], corners)
    tr = argmin(c -> Tuple(c)[1] - Tuple(c)[2], corners)
    br = argmin(c -> -Tuple(c)[1] - Tuple(c)[2], corners)

    return ((tl,bl,tr,br))
end


function makenormalizedpoints(
            (tl,bl,tr,br) :: NTuple{4, CartesianIndex{2}}, 
            bordercoords :: Vector{CartesianIndex{2}}
        ) :: Tuple{NTuple{4, Vector{Float64}},Vector{Vector{Float64}}}
    scale = 1 #maximum(Tuple(br - tl))
    function f(c)
        (y,x) = Tuple(c .- tl)
        return [x/scale, y/scale] #Point(x/scale, y/scale, img[c])
    end
    scaled = map(f, bordercoords)
    tln = f(tl)
    bln = f(bl)
    trn = f(tr)
    brn = f(br)
    return ((tln,bln,trn,brn), scaled)
end

function getSegments((tl,bl,tr,br), bordercoords):: NTuple{4,Vector{Vector{Float64}}}
    corners = (tl,bl,tr,br)
    initspul = Iterators.takewhile( e -> !(e in corners), bordercoords)
    restspul = Iterators.dropwhile( e -> !(e in corners), bordercoords)
    bordercoords = Iterators.flatten((restspul, initspul))
    
    segs = Vector{Vector{Vector{Float64}}}(undef, 4)
    for i in 1:4
        (head, tail) = Iterators.peel(bordercoords)
        segs[i] = collect(Iterators.flatten(([head], Iterators.takewhile( e -> !(e in corners), tail))))
        bordercoords = Iterators.dropwhile( e -> !(e in corners), tail)
    end

    function tlfirst(segs :: Vector{Vector{Vector{Float64}}}) :: Vector{Vector{Vector{Float64}}}
        eerstedeel = collect(Iterators.takewhile(l -> first(l) != tl, segs))
        restdeel = collect(Iterators.dropwhile(l -> first(l) != tl, segs))
        return append!(restdeel, eerstedeel)
    end

    segs = tlfirst(segs)
    if first(segs[2]) != tr

        push!(segs[1], bl)
        push!(segs[2], br)
        push!(segs[3], tr)
        push!(segs[4], tl)

        reverse!(segs)
        map(reverse!, segs)
        
        segs = tlfirst(segs)
    else
        push!(segs[1], tr)
        push!(segs[2], br)
        push!(segs[3], bl)
        push!(segs[4], tl)
    end
    
    return Tuple(segs)
end

function makeFittedSegments(
        cornerspix :: NTuple{4, CartesianIndex{2}},
        cornersnorm :: NTuple{4, Vector{Float64}},
        segments :: NTuple{4,Vector{Vector{Float64}}},
        ss) :: NTuple{4, Segment}

    segs = Vector(undef, 4)
    kant = 1
    for (i,j) in [(1,3),(3,4),(4,2),(2,1)]
        corners = (cornersnorm[i], cornersnorm[j])
        cornersp = (cornerspix[i], cornerspix[j])
        
        seg = copy(segments[kant])
        seg = map(v -> v - corners[1], seg)
        c2trans = corners[2]-corners[1]
        angle = -atan(c2trans[2], c2trans[1])
        mat = [cos(angle) -sin(angle); sin(angle) cos(angle)]
        seg = map(v -> mat*v, seg)

        yvals = getindex.(seg,2)
        highest = maximum(yvals)
        lowest = minimum(yvals)
        buiten = abs(highest) < abs(lowest) # y=0 is hier nog top en positief is naar onder

        xyvals = stack((getindex.(seg,1), getindex.(seg,2)), dims=1)
        spline = ParametricSpline(xyvals; s=ss[kant]) #s=0.0006
        
        segs[kant] = Segment(spline, kant, buiten, corners, cornersp)

        kant += 1
    end
    
    segs = Tuple(segs)
    return segs
end


function testwindow(xleft, ytop, width ,height)
    xright = xleft + width
    ybottom = ytop + height
    borderthickness = 5
    img = RGB.(rawimg)
    img[ytop:ybottom, [xleft:(xleft+borderthickness); xright:(xright+borderthickness)]] .= RGB(1,0,0)
    img[[ytop:(ytop+borderthickness); ybottom:(ybottom+borderthickness)], xleft:xright] .= RGB(1,0,0)
    display(img)
end

function useBounds(rawimg, xleft, ytop, width ,height)
    xright = xleft + width
    ybottom = ytop + height
    bounds = Bounds(ytop, ybottom, xleft, xright)
    img = rawimg[ytop:ybottom, xleft:xright]
    return (bounds, img)
end

function printcorners((tl,bl,tr,br), tmask, bordercoords)
    tlblob = [ tl+CartesianIndex(x,y) for x=-3:3, y=-3:3]
    blblob = [ bl+CartesianIndex(x,y) for x=-3:3, y=-3:3]
    trblob = [ tr+CartesianIndex(x,y) for x=-3:3, y=-3:3]
    brblob = [ br+CartesianIndex(x,y) for x=-3:3, y=-3:3]

    asdf = tmask .* RGB(1,0,0)
    asdf[bordercoords] .= RGB(1,1,1)

    asdf[tlblob] .= RGB(0,1,0) # groen
    asdf[blblob] .= RGB(1,1,0) # geel
    asdf[trblob] .= RGB(0,1,1) # felblauw
    asdf[brblob] .= RGB(0.8,0.2,1) # roze
    asdf
end

function makeStukje(
            corners :: NTuple{4, CartesianIndex{2}},
            cornersnorm :: NTuple{4, Vector{Float64}},
            segments :: NTuple{4,Vector{Vector{Float64}}},
            rawimg, bounds, params,ss) :: Stukje
    segs = makeFittedSegments(corners,cornersnorm,segments,ss)
    return Stukje(segs, rawimg, bounds, params)
end

function plotsplines(splines)
    plt = plot(aspect_ratio=:equal, yflip=true, size=(1000,1000))
    tvals = range(0.0, 1.0, 10000)
    for rand in splines
        output = rand.curve(tvals)
        outputx = output[1, :]
        outputy = output[2, :]

        plot!(outputx, outputy)
    end
    display(plt)
end

function comparesplinematchplot(spline1,spline2)
    plt = plot(aspect_ratio=:equal, yflip=true, size=(1000,1000))
    tvals = range(0.0, 1.0, 10000)
    
    output1 = spline1(tvals)
    output1x = output1[1, :]
    output1y = output1[2, :]
    output2 = spline2(tvals)
    output2x = spline2(1.0)[1] .-output2[1, :]
    output2y = -output2[2, :]

    plot!(output1x, output1y)
    plot!(output2x, output2y)
    display(plt)
    return plt
end


function comparesplinematchnorm(spline1,spline2)
    plt = plot(aspect_ratio=:equal, yflip=true, size=(1000,1000))
    tvals = range(0.0, 1.0, 10000)
    
    output1 = spline1(tvals)
    x1s = output1[1, :]
    y1s = output1[2, :]
    output2 = spline2(tvals)
    x2s = spline2(1.0)[1] .-output2[1, :]
    y2s = -output2[2, :]
    zipped = zip(x1s,y1s,x2s,y2s)
    return sum(splat((x1,y1,x2,y2) -> (x1-x2)^2 + (y1-y2)^2), zipped)
end



function plotstukjesplines(stukje :: Stukje)
    plt = plot(aspect_ratio=:equal, yflip=true, size=(1000,1000))
    tvals = range(0.0, 1.0, 10000)
    for rand in stukje.randen
        output = rand.curve(tvals)
        
        c1 = rand.corners[1]
        c2 = rand.corners[2] - c1
        angle = atan(c2[2], c2[1])
        mat = [cos(angle) -sin(angle); sin(angle) cos(angle)]
        output = mat*output

        outputx = output[1, :] .+ c1[1]
        outputy = output[2, :] .+ c1[2]

        plot!(outputx, outputy; label=(rand.buiten ? "uit" : "in"))
    end
    display(plt)
end

function plotsegment(seg)
    plot(Tuple.(seg), aspect_ratio=:equal, yflip=true, size=(1000,1000))
end
function plotsegment!(seg)
    plot!(Tuple.(seg), aspect_ratio=:equal, yflip=true, size=(1000,1000))
end


mutable struct State
    numberStukjes :: Int64
    connections :: Vector{NTuple{2, NTuple{2, Int64}}}
    lijstStukjes :: Vector{Stukje}
    openKanten :: Vector{NTuple{2,Int64}}
    posities :: Dict{Int64, Int64}
end

function saveState(state :: State)
    st = State(
        state.numberStukjes,
        state.connections,
        [],
        state.openKanten,
        state.posities
    )
    
    serialize("data/state", st)
end

function saveStukje(stukje :: Stukje, id :: Int64)
    io = open(string("data/stukje", id), "w")
    io = TranscodingStream(ZstdCompressor(), io)
    serialize(io, stukje)
    close(io)
end

function loadStukje(id :: Int64) :: Stukje
    io = open(string("data/stukje", id))
    io = TranscodingStream(ZstdDecompressor(), io)
    val = deserialize(io)
    close(io)
    return val
end

function loadState() :: State
    st = deserialize("data/state") :: State
    stukjes = []
    for i in 1:st.numberStukjes
        stukje = loadStukje(i)
        push!(stukjes, stukje)
    end
    st.lijstStukjes = stukjes
    return st
end

function registerStukje(st ::State, stukje :: Stukje, conn=nothing)
    st.numberStukjes += 1
    id = st.numberStukjes
    saveStukje(stukje, id)
    push!(st.lijstStukjes, stukje)
    kanten = map(k -> (id,k), 1:4)
    append!(st.openKanten, kanten)
    if conn === nothing
        # op nieuwe positie plakken
        maxpos = maximum(values(st.posities); init=0)
        st.posities[id] = maxpos + 1
    else
        # conn is een kant waar mee verbonden wordt,
        # dus op diens positie plakken
        (k1,(id2,k2)) = conn
        push!(st.connections, ((id,k1),(id2,k2)))
        pos = st.posities[id2]
        st.posities[id] = pos
        filter!(e -> !(e in[(id,k1), (id2,k2)]), st.openKanten)
    end
end


function showstukje(stukje :: Stukje) 
    b = stukje.rawimgbounds
    i = stukje.rawimg[b.ytop:b.ybottom, b.xleft:b.xright]
    display(i)
    return i
end


function getBestMatches(stukje :: Stukje, st :: State) :: Vector{Tuple{Float64, Int64, NTuple{2, Int64}, Int64}}
    opties = Vector{Tuple{Float64, Int64, NTuple{2, Int64}, Int64}}(undef, 0)

    for kant in 1:4
        function m(t)
            id = t[1]
            k = t[2]
            stuk = st.lijstStukjes[id]
            c1 = stukje.randen[kant].curve
            c2 = stuk.randen[k].curve
            score = comparesplinematchnorm(c1,c2)
            loc = st.posities[id]
            return (score, kant, t, loc)
        end
        function f(t)
            uit = stukje.randen[kant].buiten
            id = t[1]
            k = t[2]
            stuk = st.lijstStukjes[id]
            auit = stuk.randen[k].buiten
            return (uit != auit)
        end

        kopties = copy(st.openKanten)
        filter!(f, kopties)
        kopties = map(m, kopties)
        append!(opties, kopties)
    end
    
    sort!(opties)
    return opties
end

function showBestMatches(stukje :: Stukje, lijst :: Vector{Tuple{Float64, Int64, NTuple{2, Int64}, Int64}}, st :: State)
    for (score, kant, (id, k), pos) in lijst
        println(score, " curkant: ", kant, " other: ", (id,k), " at ", pos)
        comparesplinematchplot(stukje.randen[kant].curve, st.lijstStukjes[id].randen[k].curve)
        readline()
        showstukje(st.lijstStukjes[id])
        readline()
    end
end

######################################################################
######################################################################
######################################################################
######################################################################
######################################################################
######################################################################
######################################################################
######################################################################




#### initial state
st = State(0, [], [], [], Dict())
#### of save load spul
st = loadState()
saveState(st)




##### pak nieuwe foto
#rawimg = getNewestImage()
#rawimg = load("PXL_20241130_141241879.jpg")
getIPImage("http://192.168.2.11:8080/photoaf.jpg")
size(rawimg)

##### fix bounding box
xleft = 1000; ytop = 1600; width = 1500; height = 1500;
testwindow(xleft, ytop, width ,height)
(bounds, img) = useBounds(rawimg, xleft, ytop, width, height); img

##### maak mask
params = (1.2,2,0.4,0.7); refinemask(img,params) #params = (1,2,0.5,0.7);
mask = getmask(img, params); Gray.(mask)
img .* (mask .* 0.75 .+ 0.25)

#### maak border en corners
border = makeborder(mask); Gray.(border)
(bordercoords, tborder, tmask) = thinborderupdatemask(border, mask);
corners = getcorners(bordercoords, tborder, tmask); printcorners(corners,tmask,bordercoords)
(cornersnorm, bordercoordsn) = makenormalizedpoints(corners, bordercoords); plotsegment(bordercoordsn)
segments = getSegments(cornersnorm, bordercoordsn); plotsegment(segments[1]); plotsegment!(segments[2]); plotsegment!(segments[3]); plotsegment!(segments[4])

println(map(s -> collect(Iterators.take(reverse(s),10)),segments))

#### maak fits
ss = [5000,5000,5000,5000];
stukje = makeStukje(corners,cornersnorm,segments, rawimg, bounds, params, ss); plotstukjesplines(stukje)

#### Sorteer passende stukjes
lijst = getBestMatches(stukje, st)
showBestMatches(stukje, lijst, st)


#### Kies en store
# registerStukje(st, stukje) of registerStukje(st, stukje, (kant,(id2,k2)))
registerStukje(st, stukje)



#### Saveload state
saveState(st)
st = loadState()