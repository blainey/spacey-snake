package main

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"
	"sort"
	"sync"
	"sync/atomic"
	"time"
)

// ----------------------------------------------------------------
// JSON types
// ----------------------------------------------------------------

type Coord struct {
	X int `json:"x"`
	Y int `json:"y"`
}

type Snake struct {
	ID     string  `json:"id"`
	Name   string  `json:"name"`
	Health int     `json:"health"`
	Body   []Coord `json:"body"`
}

type Game struct {
	ID string `json:"id"`
}

type Board struct {
	Height int     `json:"height"`
	Width  int     `json:"width"`
	Food   []Coord `json:"food"`
	Snakes []Snake `json:"snakes"`
}

type StartRequest struct {
	Game  Game  `json:"game"`
	Turn  int   `json:"turn"`
	Board Board `json:"board"`
	You   Snake `json:"you"`
}

type StartResponse struct {
	Color    string `json:"color,omitempty"`
	HeadType string `json:"headType,omitempty"`
	TailType string `json:"tailType,omitempty"`
}

type EndRequest struct {
	Game  Game  `json:"game"`
	Turn  int   `json:"turn"`
	Board Board `json:"board"`
	You   Snake `json:"you"`
}

type MoveRequest struct {
	Game  Game  `json:"game"`
	Turn  int   `json:"turn"`
	Board Board `json:"board"`
	You   Snake `json:"you"`
}

type MoveResponse struct {
	Move  string `json:"move"`
	Shout string `json:"shout,omitempty"`
}

// ----------------------------------------------------------------
// Utility functions
// ----------------------------------------------------------------

// Absolute value
func Abs (x int) int {
	if x < 0 {
		return -x
	} else {
		return x
	}
}

// Compute manhattan distance between two cells
func ManDist (a, b Coord) int {
	return Abs(a.X-b.X) + Abs(a.Y-b.Y)
}

// Translate a coordinate
func Translate (a Coord, dx, dy int) Coord {
	return Coord{ a.X+dx, a.Y+dy }
}

// ----------------------------------------------------------------
// Game Context
// ----------------------------------------------------------------

type ContextType struct {
	color string
	heads map[string]Coord
	food []Coord
}

var gameContext struct {
	sync.RWMutex
	m map[string]*ContextType
}

// ----------------------------------------------------------------
// Logging
// ----------------------------------------------------------------
	
type Log struct {
	color string
	level string
}

func NewLogger (ID string, level string) Log {
	var l Log
	gameContext.RLock()
	l.color = gameContext.m[ID].color
	gameContext.RUnlock()
	l.level = level
	return l
}

func (l Log) Printf (s string, msgs ...interface{}) {
	fmt.Printf("%s(%s):",l.level,l.color)
	fmt.Printf(s,msgs...)
}

// ----------------------------------------------------------------
// GameCell
// ----------------------------------------------------------------

type GameCell struct {
	content		uint16
	space		uint16
}

func (c GameCell) IsEmpty() bool {
	return c.content == 0
}

func (c GameCell) IsFood() bool {
	return c.content == 1
}

func (c GameCell) IsBody() bool {
	return c.content > 2 && c.content % 3 == 0
}

func (c GameCell) IsHead() bool {
	return c.content > 2 && c.content % 3 == 1
}

func (c GameCell) IsTail() bool {
	return c.content > 2 && c.content % 3 == 2
}

func (c GameCell) IsSelf() bool {
	return c.content > 2 && c.content / 3 == 1
}

func (c GameCell) SnakeNo() int {
	return int(c.content) / 3 - 1
}

func FoodCell() GameCell { 
	return GameCell { 1, 0 }
}

func BodyCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s+1) * 3
	return c
}

func HeadCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s+1) * 3 + 1
	return c
}

func TailCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s+1) * 3 + 2
	return c
}

// ----------------------------------------------------------------
// SnakeState
//
// We track the head and tail o feach snake, its length and 
// the distance from its head to our head
// ----------------------------------------------------------------

type SnakeState struct {
	ID		 string
	head 	 Coord
	tail 	 Coord
	length 	 int
	segments []Coord
	dist	 int
	growing  bool
}

// ----------------------------------------------------------------
// SpaceState
//
// We track the size and boundary of each spatial region around
// the head of our snake.  The boundary is a set of snakes
// that make up some part of it (in addition to possibly the 
// edges of the grid)
// ----------------------------------------------------------------

type SpaceState struct {
	size	int
	snakes	[]bool
	nsnakes	int
	self	bool
	nfood	int
}

// ----------------------------------------------------------------
// FoodState
//
// We track the position of each food disc and the distance 
// between the food and the head of our snake
// ----------------------------------------------------------------

type FoodState struct {
	pos				Coord
	dist			int
	closerSnakes	int
}

// ----------------------------------------------------------------
// GameState
//
// An aggregation of information about the current game state
// ----------------------------------------------------------------

type GameState struct {
	ID		string
	debug	Log
	info	Log
	color	string
	turn	int
	h, w	int
	grid 	[][]GameCell
	snakes	[]SnakeState
	food	[]FoodState
	spaces	[4]SpaceState
}

func (s *GameState) IsEmpty(c Coord) bool {
	return s.grid[c.X][c.Y].IsEmpty()
}

func (s *GameState) IsFood(c Coord) bool {
	return s.grid[c.X][c.Y].IsFood()
}

func (s *GameState) IsBody(c Coord) bool {
	return s.grid[c.X][c.Y].IsBody()
}

func (s *GameState) IsHead(c Coord) bool {
	return s.grid[c.X][c.Y].IsHead()
}

func (s *GameState) IsTail(c Coord) bool {
	return s.grid[c.X][c.Y].IsTail()
}

func (s *GameState) IsSelf(c Coord) bool {
	return s.grid[c.X][c.Y].IsSelf()
}

func (s *GameState) SnakeNo(c Coord) int {
	return s.grid[c.X][c.Y].SnakeNo()
}

// ----------------------------------------------------------------
// Generic traversal of neighboring cells
// ----------------------------------------------------------------
func (s *GameState) VisitNeighbours (c Coord, visitor func(Coord,string)) {
	left := c; left.X--
	if left.X >= 0 { visitor(left,"left") }

	right := c; right.X++
	if right.X < s.w { visitor(right,"right") }

	up := c; up.Y--
	if up.Y >= 0 { visitor(up,"up") }

	down := c; down.Y++
	if down.Y < s.h { visitor(down,"down") }
}

// ----------------------------------------------------------------
// Space Mapping
//
// This is a flood fill algorithm which is used to map out a
// space adjacent to the head of our snake.  A space is any set 
// of cells bounded by the bodies or heads of snakes, either
// our own or others.
// ----------------------------------------------------------------
func (s *GameState) MapSpace (c Coord, space int) int {
	stack := make([]Coord, s.h * s.w * 4)
	top := 0
	stack[top] = c

	s.spaces[space].snakes = make([]bool, len(s.snakes)+1)

	count := 0
	for top >= 0 {
		p := stack[top]
		top--

		pcell := s.grid[p.X][p.Y]
		if (pcell.space != 0) { continue }

		count++
		s.grid[p.X][p.Y].space = uint16(space)
		if pcell.IsFood() { s.spaces[space].nfood++ }

		s.VisitNeighbours (p, func (neighbour Coord, dir string) {
			if s.IsEmpty(neighbour) || s.IsFood(neighbour) || s.IsTail(neighbour) {
				top++
				stack[top] = neighbour
			} else if s.IsBody(neighbour) || s.IsHead(neighbour) {
				s.spaces[space].snakes[s.SnakeNo(neighbour)] = true
			}
		})

	}

	return count
}

// ----------------------------------------------------------------
// Initialize GameState
//
// Based on data found in request payload.
// ----------------------------------------------------------------

func (s *GameState) Initialize (g Game, t int, b Board, y Snake) {
	s.ID = g.ID
	s.turn = t

	s.h = b.Height
	s.w = b.Width
	
	s.grid = make ([][]GameCell, s.w)
	for i := range s.grid {
		s.grid[i] = make([]GameCell, s.h)
	}

	myHead := y.Body[0]

	foodLastTurn := make(map[Coord]bool)
	gameContext.RLock()
	context := gameContext.m[y.ID]
	gameContext.RUnlock()
	for _,food := range context.food {
		foodLastTurn[food] = true
	}

	s.snakes = make ([]SnakeState, 0, len(b.Snakes))

	for _,snake := range b.Snakes {
		var this SnakeState
		this.ID = snake.ID

		this.segments = make([]Coord,0,len(snake.Body))
		smap := make(map[Coord]bool)
		for _,segment := range snake.Body {
			if _,ok := smap[segment]; ok { continue }
			smap[segment] = true
			this.segments = append(this.segments,segment)
		}
		this.length = len(this.segments)

		this.head = this.segments[0]
		this.dist = ManDist(this.head,myHead)
		this.growing = (t < 2 || foodLastTurn[this.head])

		this.tail = this.segments[this.length-1]

		s.snakes = append(s.snakes,this)
	}

	// Sort snakes in order of distance of their head from our head
	// This will put our snake at index 0
	sort.Slice(s.snakes, func(i, j int) bool {
		return s.snakes[i].dist < s.snakes[j].dist
	})

	// Enter snake ID into all segment cells
	for sx,snake := range s.snakes {
		for _,segment := range snake.segments {
			s.grid[segment.X][segment.Y] = BodyCell(sx)
		}
		s.grid[snake.head.X][snake.head.Y] = HeadCell(sx)
		s.grid[snake.tail.X][snake.tail.Y] = TailCell(sx)
	}

	for _,snake := range s.snakes {
		growing := ""
		if snake.growing { growing = " growing" }
		s.debug.Printf("Snake at: [H](%d,%d), [T](%d,%d), len=%d, dist=%d%s\n",
					   snake.head.X,snake.head.Y,snake.tail.X,snake.tail.Y,
					   snake.length,snake.dist,growing)
	}

	s.food = make ([]FoodState, 0, len(b.Food))

	fmap := make(map[Coord]bool)
	for _,food := range b.Food {
		if _,ok := fmap[food]; ok { continue }
		fmap[food] = true

		s.grid[food.X][food.Y] = FoodCell()

		var this FoodState 
		this.pos = food
		this.dist = ManDist(food,myHead)

		// How many snakes are close to this food than us?
		this.closerSnakes = 0
		for _,snake := range s.snakes {
			if ManDist(snake.head,food) < this.dist {
				this.closerSnakes++
			}
		}

		s.food = append(s.food,this)
	}

	// Sort food in order of distance from our head
	sort.Slice(s.food, func(i, j int) bool {
		return s.food[i].dist < s.food[j].dist
	})
	for _,food := range s.food {
		s.debug.Printf("Food at: (%d,%d), dist=%d\n", food.pos.X,food.pos.Y,food.dist)
	}


}

// ----------------------------------------------------------------
// FindMove
//
// Decide on a move.
// ----------------------------------------------------------------

func FindMove (g Game, t int, b Board, y Snake) string {
	start := time.Now()

	var s GameState
	s.debug = NewLogger(y.ID, "DEBUG")
	s.info = NewLogger(y.ID, "INFO")

	s.info.Printf("-------------------------------------------------------\n")
	s.info.Printf("Move turn=%d\n", t)

	Result := func(dir string) string {
		elapsed := time.Since(start)
		s.info.Printf("Move result=%s, elapsed=%dms\n", dir, elapsed.Milliseconds())
		return dir
	}

	Left  := func() string { return Result("left")  }
	Right := func() string { return Result("right") }
	Up    := func() string { return Result("up")    }
	Down  := func() string { return Result("down")  }

	s.Initialize(g,t,b,y)

	myHead := s.snakes[0].head
	myLength := s.snakes[0].length
	//myHealth := y.Health

	//s.debug.Printf("My head:(%d,%d), length:%d, health:%d\n",myHead.X,myHead.Y,myLength,myHealth)

	if t == 0 {
		// Special case, we can move in any direction, so just move toward the closest food
		cf := s.food[0].pos
		s.debug.Printf("Turn=0 special case, head=(%d,%d), cf=(%d,%d)\n",myHead.X,myHead.Y,cf.X,cf.Y)
		switch {
			case cf.X < myHead.X: return Left()
			case cf.X > myHead.X: return Right()
			case cf.Y < myHead.Y: return Up()
			default: return Down()
		}
	}

 	// Now, there are up to three possible directions we can move, since our own body
	// will block at least one direction
	type MoveType struct {
		dir 		string
		c 			Coord
		nlonger 	int
		alternate   int
		nshorter	int
		space 		int
		smallSpace	bool
	}
	moves := make([]MoveType,0,4)

	s.VisitNeighbours (myHead, func (neighbour Coord, dir string) {
		if s.IsBody(neighbour) || s.IsHead(neighbour) || 
		   (s.IsTail(neighbour) && s.snakes[s.SnakeNo(neighbour)].growing) {
			//s.debug.Printf("Direction %s blocked by snake\n", dir)
		} else {
			s.debug.Printf("Add to possible moves: %s=(%d,%d)[%d]\n", dir,
						   neighbour.X, neighbour.Y, 
						   s.grid[neighbour.X][neighbour.Y].content)
			var move MoveType
			move.dir = dir
			move.c = neighbour
			moves = append(moves,move)
		}
	})

	/*
	nopen := len(moves)

	switch nopen {
	case 0: 
		s.debug.Printf("Suicide!\n")
		return Left()
	case 1:
		s.debug.Printf("Select %s because it is the only viable move\n", moves[0].dir)
		return Result(moves[0].dir)
	}
	*/

	// If any moves have an adjacent head from a longer snake, then avoid those moves
	// If these moves have an adjacent head from a shorter snake, move to take it out
	// unless we are in critical health

	allLongerSnakes := true
	for index,move := range moves {
		moves[index].nlonger = 0
		moves[index].nshorter = 0

		s.VisitNeighbours (move.c, func (neighbour Coord, dir string) {
			if s.IsHead(neighbour) && neighbour != myHead {
				if s.snakes[s.SnakeNo(neighbour)].length >= myLength {
					moves[index].nlonger++
					// count other moves available to this snake
					s.VisitNeighbours (neighbour, func (nextNeighbour Coord, dir string) {
						if nextNeighbour != move.c && 
						   (!s.IsBody(nextNeighbour) && !s.IsHead(nextNeighbour)) {
							moves[index].alternate++
							if s.IsFood(nextNeighbour) { 
								moves[index].alternate += 4
							}
						}
					})
				} else {
					moves[index].nshorter++
				}
			}
		})

		if moves[index].nlonger == 0 { allLongerSnakes = false } 
	}
	
	/*
	switch nopen {
		case 0: 			
			least := 0
			for index,move := range moves {
				if move.nlonger < moves[index].nlonger { least = index }
			}
			dir := moves[least].dir
			if len(moves) > 1 && s.IsFood(moves[least].c) {
				// choose square without food
				for _,move := range moves {
					if !s.IsFood(move.c) {
						dir = move.dir
						break
					}
				}
			}
			s.debug.Printf("Select %s as the only option even though it is known to be unsafe\n",dir)
			return Result(dir)

		case 1:
			dir := "none"
			for _,move := range moves {
				if move.nlonger == 0 { 
					dir = move.dir 
					break
				}
			}
			if dir == "none" { panic("Unable to find valid move") }
			s.debug.Printf("Select %s because it is the only viable move\n", dir)
			return Result(dir)
	}
	*/

	// Map spaces anchored at each valid adjacent cell
	nspaces := 0
	for index,move := range moves {
		if (s.grid[move.c.X][move.c.Y].space > 0) { 
			moves[index].space = int(s.grid[move.c.X][move.c.Y].space)
			continue 
		} else {
			nspaces++
			moves[index].space = nspaces
		}

		s.spaces[nspaces].size = s.MapSpace(move.c,nspaces)
		//s.debug.Printf("Space %d, direction %s, size %d\n", nspaces, move.dir,
		//               s.spaces[nspaces].size)

		// Count the number of snakes bounding the space
		//s.debug.Printf("Count snakes bounding the space\n")
		nsnakes := 0
		for _,snakeInSpace := range s.spaces[nspaces].snakes {
			if (snakeInSpace) { nsnakes++ }
		}
		s.spaces[nspaces].nsnakes = nsnakes
		s.spaces[nspaces].self = (nsnakes == 1 && s.spaces[nspaces].snakes[0])
	}

	// For spaces which are bounded by just our snake, we should not enter if the size is
	// smaller than half our length minus the number of food discs in the space.  The reason
	// is that, worst case, we will enter the region, eat all the food and grow our length
	// by that much.
	//
	// For other spaces, we should not enter if the size of the space is smaller than our 
	// length.  This is conservative since the boundign snakes will be moving so other 
	// heuristics are possible here.

	allSmallSpaces := true
	for index,move := range moves {
		if (move.nlonger > 0) { continue }

		space := s.grid[move.c.X][move.c.Y].space	
		/*	
		if s.spaces[space].self {
			if s.spaces[space].size < myLength/2 - s.spaces[space].nfood {
				s.debug.Printf("Avoid %s because it is a self-bounded space that is too small\n", move.dir)
				moves[index].smallSpace = true
				nopen--
				continue
			}	
		} else */ if s.spaces[space].size < myLength {
			//s.debug.Printf("Avoid %s because it is a space that is too small\n", move.dir)
			moves[index].smallSpace = true
			continue
		}

		allSmallSpaces = false
	}

	/*
	switch nopen {
	case 0:
		// Here, we should just choose the largest space
		most := -1
		for index,move := range moves {
			if most < 0 || s.spaces[move.space].size > s.spaces[moves[most].space].size { 
				most = index 
			}
		}
		s.debug.Printf("Select %s which is a small space but the only option", moves[most].dir)
		return Result(moves[most].dir)

	case 1:
		dir := "none"
		for _,move := range moves {
			if move.nlonger == 0 && !move.smallSpace { 
				dir = move.dir 
				break
			}
		}
		if dir == "none" { panic("Unable to find valid move") }
		s.debug.Printf("Select %s because it is the only viable move\n", dir)
		return Result(dir)
	}
	*/

	// TODO: at this point, we can choose to chase food, prefer a larger space to move into,
	// or aim to attack smaller snakes.

	// Choose the best move 
	least := -1
	leastDist := s.h + s.w
	s.debug.Printf("Decide on bext move\n")
	for index,move := range moves {
		// Don't get trapped in small spaces, unless its our only move
		if move.smallSpace { 
			s.debug.Printf("Direction %s is a small space\n", move.dir)

			// Is it our only move?
			if len(moves) == 1 { 
				s.debug.Printf("Go in this direction anyway since its our ownly choice\n")
				return Result(move.dir) 
			}

			// Are all of our moves into small spaces?
			if allSmallSpaces {
				// Choose the largest of them
				largest := 0
				for mx,mv := range moves {
					if s.spaces[mv.space].size > s.spaces[moves[largest].space].size {
						largest = mx
					}
				}

				s.debug.Printf("All our choices are small spaces, so choose direction %s which is th elargest of them\n",moves[largest].dir)
				return Result(moves[largest].dir)
			}

			continue
		}

		// Avoid going head to head with a longer snake
		if move.nlonger > 0 { 
			s.debug.Printf("Direction %s is threatened by a longer snake\n", move.dir)

			// Is it our only move?
			if len(moves) == 1 { 
				s.debug.Printf("Go in this direction anyway since its our ownly choice\n")
				return Result(move.dir) 
			}

			// Are all of our moves against longer snakes?
			if allLongerSnakes {
				// Choose the one most likely to avoid a collision,
				// i.e. nlonger is smallest and among equal number of longer snakes
				// there are greater alternatives
				best := 0
				for mx,mv := range moves {
					if mv.nlonger < moves[best].nlonger ||
					   (mv.nlonger == moves[best].nlonger && mv.alternate > moves[best].alternate) {
						best = mx
					}
				}

				s.debug.Printf("All our choices are threatened by longer snakes, so choose direction %s which where the longer snakes have more alternatives\n",moves[best].dir)
				return Result(moves[best].dir)
			}

			continue 
		}

		if s.IsFood(move.c) { 
			s.debug.Printf("Select %s because there is a food disc there\n", move.dir)
			return Result(move.dir) 
		}

		if move.nshorter > 0 {
			s.debug.Printf("Select %s because we have the opportunity to eat a shorter snake\n", move.dir)
			return Result(move.dir)
		}

		dist := s.h + s.w
		for _,food := range s.food {
			mdist := ManDist(move.c,food.pos)
			if mdist < food.dist && (len(s.snakes) < 3 || food.closerSnakes == 0) {
				dist = mdist		
				break;
			}
		}

		if dist == s.h + s.w {
			for _,food := range s.food {
				mdist := ManDist(move.c,food.pos)
				if mdist < food.dist {
					dist = mdist		
					break;
				}
			}	
		}

		if least < 0 || dist < leastDist { 
			least = index
			leastDist = dist
		}
	}

	s.debug.Printf("Select %s because it makes the best progress toward food\n", moves[least].dir)
	return Result(moves[least].dir)
}

func UpdateContext (id string, s []Snake, f []Coord) {
	gameContext.Lock()
	gameContext.m[id].heads = make(map[string]Coord)
	for _,snake := range s {
		gameContext.m[id].heads[snake.ID] = snake.Body[0]
	}
	fvec := make([]Coord,0,len(f))
	fmap := make(map[Coord]bool)
	for _,food := range f {
		if _,ok := fmap[food]; ok { continue }
		fmap[food] = true
		fvec = append(fvec,food)
	}
	gameContext.m[id].food = fvec
	gameContext.Unlock()
}

// HandleMove is called for each turn of each game.
// Valid responses are "up", "down", "left", or "right".
func HandleMove(w http.ResponseWriter, r *http.Request) {
	request := MoveRequest{}
	json.NewDecoder(r.Body).Decode(&request)

	direction := FindMove (request.Game, request.Turn, request.Board, request.You)

	response := MoveResponse { direction, "" }

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(response)

	UpdateContext(request.You.ID, request.Board.Snakes, request.Board.Food)
}

// HandleStart is called at the start of each game your Battlesnake is playing.
// The StartRequest object contains information about the game that's about to start.
var colorPicker uint32
func HandleStart(w http.ResponseWriter, r *http.Request) {
	request := StartRequest{}
	json.NewDecoder(r.Body).Decode(&request)

	var colors = []struct {
		name	string
		hexcode	string
	} {
		{ "red",	"#cc0000" },	
		{ "blue",	"#0000cc" },
		{ "green",	"#006600" },
		{ "tan",	"#996633" },
		{ "pink",	"#ff66ff" },
		{ "yellow",	"#ffff00" },
		{ "violet",	"#cc0099" },
	}  
	
	cx := atomic.AddUint32 (&colorPicker, 1) % (uint32)(len(colors))

	response := StartResponse{
		Color:    colors[cx].hexcode,
		HeadType: "evil",
		TailType: "skinny",
	}

	gameContext.Lock()
	id := request.You.ID
	gameContext.m[id] = new(ContextType)
	gameContext.m[id].color = colors[cx].name
	gameContext.Unlock()

	UpdateContext(request.You.ID, request.Board.Snakes, request.Board.Food)

	fmt.Printf("INFO(%s): Start\n", colors[cx].name)
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(response)
}

// HandleEnd is called when a game your Battlesnake was playing has ended.
// It's purely for informational purposes, no response required.
func HandleEnd(w http.ResponseWriter, r *http.Request) {
	request := EndRequest{}
	json.NewDecoder(r.Body).Decode(&request)

	gameContext.Lock()
	delete(gameContext.m,request.You.ID)
	gameContext.Unlock()
	
	// Nothing to respond with here
	fmt.Print("END\n")
}

func main() {
	port := os.Getenv("PORT")
	if len(port) == 0 {
		port = "8080"
	}

	gameContext.m = make(map[string]*ContextType)

	http.HandleFunc("/", func (w http.ResponseWriter, r *http.Request) {
		fmt.Fprint(w, "Spacey Snake is alive!")
	})

	http.HandleFunc("/ping", func (w http.ResponseWriter, r *http.Request) {
		fmt.Fprint(w, "One ping only please.")
	})	

	http.HandleFunc("/start", HandleStart)
	http.HandleFunc("/move", HandleMove)
	http.HandleFunc("/end", HandleEnd)

	fmt.Printf("Starting Battlesnake Server at http://0.0.0.0:%s...\n", port)
	log.Fatal(http.ListenAndServe(":"+port, nil))
}
