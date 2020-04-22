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
// Logging
// ----------------------------------------------------------------

var mySnakes struct {
	sync.RWMutex
	m map[string]string
}
	
type Log struct {
	color string
	level string
}

func NewLogger (ID string, level string) Log {
	var l Log
	mySnakes.RLock()
	l.color = mySnakes.m[ID]
	mySnakes.RUnlock()
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
	return c.content % 3 == 0
}

func (c GameCell) IsHead() bool {
	return c.content % 3 == 1
}

func (c GameCell) IsTail() bool {
	return c.content % 3 == 2
}

func (c GameCell) IsSelf() bool {
	return c.content / 3 == 1
}

func (c GameCell) SnakeNo() int {
	return int(c.content) / 3
}

func FoodCell() GameCell { 
	return GameCell { 1, 0 }
}

func BodyCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s) * 3
	return c
}

func HeadCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s) * 3 + 1
	return c
}

func TailCell(s int) GameCell {
	var c GameCell
	c.content = uint16(s) * 3 + 2
	return c
}

// ----------------------------------------------------------------
// SnakeState
//
// We track the head and tail o feach snake, its length and 
// the distance from its head to our head
// ----------------------------------------------------------------

type SnakeState struct {
	ID		string
	head 	Coord
	tail 	Coord
	length 	int
	dist	int
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
	pos		Coord
	dist	int
}

// ----------------------------------------------------------------
// GameState
//
// An aggregation of information about the current game state
// ----------------------------------------------------------------

type GameState struct {
	ID		string
	color	string
	turn	int
	h, w	int
	grid 	[][]GameCell
	snakes	[]SnakeState
	food	[]FoodState
	spaces	[4]SpaceState
}

func (s GameState) IsEmpty(c Coord) bool {
	return s.grid[c.X][c.Y].IsEmpty()
}

func (s GameState) IsFood(c Coord) bool {
	return s.grid[c.X][c.Y].IsFood()
}

func (s GameState) IsBody(c Coord) bool {
	return s.grid[c.X][c.Y].IsBody()
}

func (s GameState) IsHead(c Coord) bool {
	return s.grid[c.X][c.Y].IsHead()
}

func (s GameState) IsTail(c Coord) bool {
	return s.grid[c.X][c.Y].IsTail()
}

func (s GameState) IsSelf(c Coord) bool {
	return s.grid[c.X][c.Y].IsSelf()
}

func (s GameState) SnakeNo(c Coord) int {
	return s.grid[c.X][c.Y].SnakeNo()
}

// ----------------------------------------------------------------
// Space Mapping
//
// This is a flood fill algorithm which is used to map out a
// space adjacent to the head of our snake.  A space is any set 
// of cells bounded by the bodies or heads of snakes, either
// our own or others.
// ----------------------------------------------------------------

func (s GameState) MapSpace (c Coord, space int) int {
	if s.grid[c.X][c.Y].space != 0 { return 0 }

	count := 1
	s.grid[c.X][c.Y].space = uint16(space)
	if s.grid[c.X][c.Y].IsFood() { s.spaces[space].nfood++ }

	IsOpen := func (c Coord) bool {
		return s.IsEmpty(c) || s.IsFood(c) || s.IsTail(c)
	}

	TrackSnake := func (c Coord) {
		if (s.IsBody(c) || s.IsHead(c)) { 
			s.spaces[space].snakes[s.SnakeNo(c)] = true 
		}
	}

	west := c; c.X--
	if west.X >= 0 {
		if IsOpen(west)  { 
			count += s.MapSpace(west,space) 
		} else { 
			TrackSnake(west) 
		}
	} 

	north := c; north.Y--
	if north.Y >= 0 {
		if IsOpen(north) { 
			count += s.MapSpace(north,space) 
		} else { 
			TrackSnake(north) 
		}
	}

	east := c; c.X++
	if east.X < s.w {
		if IsOpen(east) { 
			count += s.MapSpace(east,space) 
		} else { 
			TrackSnake(east) 
		}
	} 

	south := c; south.Y++
	if south.Y < s.h {
		if IsOpen(south) { 
			count += s.MapSpace(south,space) 
		} else { 
			TrackSnake(south) 
		}
	}

	return count
}

// ----------------------------------------------------------------
// Initialize GameState
//
// Based on data found in request payload.
// ----------------------------------------------------------------

func (s GameState) Initialize (g Game, t int, b Board, y Snake) {
	debug := NewLogger(y.ID, "DEBUG")
	//info := NewLogger(y.ID, "INFO")

	s.ID = g.ID
	s.turn = t

	s.h = b.Height
	s.w = b.Width
	
	debug.Printf("Allocate game grid\n")
	s.grid = make ([][]GameCell, s.w)
	for i := range s.grid {
		s.grid[i] = make([]GameCell, s.h)
	}

	debug.Printf("Allocate snakes vector\n")
	s.snakes = make ([]SnakeState, len(b.Snakes))

	myHead := y.Body[0]

	debug.Printf("Plot snakes on grid\n")
	for sx,snake := range b.Snakes {
		s.snakes[sx].ID = snake.ID

		head := snake.Body[0]
		s.snakes[sx].head = head
		s.grid[head.X][head.Y] = HeadCell(sx)

		sz := len(snake.Body)
		s.snakes[sx].length = sz
		for i := 1; i < sz-1; i++ {
			pos := snake.Body[i]
			s.grid[pos.X][pos.Y] = BodyCell(sx)
		}

		tail := snake.Body[sz-1]
		s.snakes[sx].tail = tail
		s.grid[tail.X][tail.Y] = TailCell(sx)

		s.snakes[sx].dist = ManDist(head,myHead)
	}

	// Sort snakes in order of distance of their head from our head
	// This will put our snake at index 0
	debug.Printf("Sort snakes by distance\n")
	sort.Slice(s.snakes, func(i, j int) bool {
		return s.snakes[i].dist < s.snakes[j].dist
	})

	debug.Printf("Allocate food vector\n")
	s.food = make ([]FoodState, len(b.Food))

	debug.Printf("Plot food discs on grid\n")
	for fx,food := range b.Food {
		s.grid[food.X][food.Y] = FoodCell()
		s.food[fx].pos = food
		s.food[fx].dist = ManDist(food,myHead)
	}

	// Sort food in order of distance from our head
	debug.Printf("Sort food discs by distance\n")
	sort.Slice(s.food, func(i, j int) bool {
		return s.food[i].dist < s.food[j].dist
	})
}

// ----------------------------------------------------------------
// FindMove
//
// Decide on a move.
// ----------------------------------------------------------------

func FindMove (g Game, t int, b Board, y Snake) string {
	start := time.Now()

	debug := NewLogger(y.ID, "DEBUG")
	info := NewLogger(y.ID, "INFO")

	info.Printf("Move turn=%d\n", t)

	Result := func(dir string) string {
		elapsed := time.Since(start)
		info.Printf("Move result=%s, elapsed=%dms\n", dir, elapsed.Milliseconds())
		return dir
	}

	Left  := func() string { return Result("left")  }
	Right := func() string { return Result("right") }
	Up    := func() string { return Result("up")    }
	Down  := func() string { return Result("down")  }

	var s GameState
	s.Initialize(g,t,b,y)
	head := s.snakes[1].head

	if (t == 0) {
		// Special case, we can move in any direction, so just move toward the closest food
		cf := s.food[0].pos
		switch {
		case cf.X < head.X: return Left()
		case cf.X > head.X: return Right()
		case cf.Y < head.Y: return Up()
		default: return Down()
		}
	}

	LeftCell := func (c Coord) (Coord,bool) {
		c.X--
		return c, c.X >= 0
	}
	RightCell := func (c Coord) (Coord,bool) {
		c.X++
		return c, c.X < s.w
	}
	UpCell := func (c Coord) (Coord,bool) {
		c.Y--
		return c, c.Y >= 0
	}
	DownCell := func (c Coord) (Coord,bool) {
		c.Y++
		return c, c.Y < s.h
	}

 	// Now, there are up to three possible directions we can move, since our own body
	// will block at least one direction
	var moves [3]struct {
		dir string
		c Coord
	}

	IsBlocked := func (c Coord) bool {
		return s.IsBody(c) || s.IsHead(c)
	}

	nmoves := 0

	left, okLeft := LeftCell(head)
	if okLeft && !IsBlocked(left) { 
		moves[nmoves].dir = "left"
		moves[nmoves].c = left
		nmoves++
	}
	
	right, okRight := RightCell(head)
	if okRight && !IsBlocked(right) {
		moves[nmoves].dir = "right"
		moves[nmoves].c = right
		nmoves++
	}

	up, okUp := UpCell(head)
	if okUp && !IsBlocked(up) {
		moves[nmoves].dir = "up"
		moves[nmoves].c = up
		nmoves++
	}

	down, okDown := DownCell(head) 
	if okDown && !IsBlocked(down) {
		moves[nmoves].dir = "down"
		moves[nmoves].c = down
		nmoves++
	}

	if (nmoves == 0) {
		debug.Printf("Suicide!")
		return Left()
	}

	if (nmoves == 1) {
		debug.Printf("Select %s because it is the only viable move")
		return Result(moves[0].dir)
	}

	// Map spaces anchored at each valid adjacent cell
	nspaces := 0
	for _,move := range moves {
		if (s.grid[move.c.X][move.c.Y].space > 0) { continue }

		nspaces++
		s.spaces[nspaces].size = s.MapSpace(move.c,nspaces)

		// Count the number of snakes bounding the space
		nsnakes := 0
		for _,snakeInSpace := range s.spaces[nspaces].snakes {
			if (snakeInSpace) { nsnakes++ }
		}
		s.spaces[nspaces].nsnakes = nsnakes
		s.spaces[nspaces].self = nsnakes == 1 && s.spaces[nspaces].snakes[1]
	}

	// Rule out moves where we'd be entering a space where there is too little room for us
	Exclude := func (x int) {
		for i := x+1; i < nmoves; i++ {
			moves[i-1] = moves[i]
		} 
		nmoves--
	}

	// For spaces which are bounded by just our snake, we should not enter if the size is
	// smaller than half our length plus the number of food discs in the space.  The reason
	// is that, worst case, we will enter the region, eat all the food and grow our length
	// by that much.
	//
	// For other spaces, we should not enter if the size of the space is smaller than our 
	// length.  This is conservative since the boundign snakes will be moving so other 
	// heuristics are possible here.

	myLength := s.snakes[1].length
	for mx := 0; mx < nmoves; {
		move := moves[mx]
		space := s.grid[move.c.X][move.c.Y].space
		if s.spaces[space].self {
			if s.spaces[space].size < myLength/2 + s.spaces[space].nfood {
				debug.Printf("Exclude %s because it is a self-bounded region that is too small", move.dir)
				Exclude(mx)
				continue
			}	
		} else if s.spaces[space].size < myLength {
			debug.Printf("Exclude %s because it is a region that is too small", move.dir)
			Exclude(mx)
			continue
		}
		mx++
	}

	if (nmoves == 0) {
		debug.Printf("Suicide!")
		return Left()
	}

	if (nmoves == 1) {
		debug.Printf("Select %s because it is the only viable move")
		return Result(moves[0].dir)
	}

	AdjacentSnakeHeads := func (c Coord) (int,int) {
		nlonger := 0
		nshorter := 0

		left, okLeft := LeftCell(c)
		if okLeft && s.IsHead(left) && left != head { 
			length := s.snakes[s.SnakeNo(left)].length
			if length >= myLength { 
				nlonger++ 
			} else {
				nshorter++
			}
		}
		
		right, okRight := RightCell(c)
		if okRight && s.IsHead(right) && right != head {
			length := s.snakes[s.SnakeNo(right)].length
			if length >= myLength { 
				nlonger++ 
			} else {
				nshorter++
			}
		}
	
		up, okUp := UpCell(c)
		if okUp && s.IsHead(up) && up != head {
			length := s.snakes[s.SnakeNo(up)].length
			if length >= myLength { 
				nlonger++ 
			} else {
				nshorter++
			}
		}
	
		down, okDown := DownCell(c) 
		if okDown && s.IsHead(down) && down != head {
			length := s.snakes[s.SnakeNo(down)].length
			if length >= myLength { 
				nlonger++ 
			} else {
				nshorter++
			}
		}

		return nlonger, nshorter
	}
	
	// If any moves have an adjacent head from a longer snake, then avoid those moves
	// If these moves have an adjacent head from a shorter snake, move to take it out
	// unless we are in critical health

	myHealth := y.Health
	for mx := 0; mx < nmoves; {
		move := moves[mx]
		nlonger, nshorter := AdjacentSnakeHeads(move.c)

		if nlonger > 0 { 
			debug.Printf("Exclude %s because it is adjacent to the head of a loner snake", move.dir)
			Exclude(mx); 
			continue 
		}

		if nshorter > 0 && myHealth > s.food[0].dist { 
			debug.Printf("Select %s because we have the opportunity to take out a shorter snake", move.dir)
			return Result(move.dir) 
		}

		mx++
	}
	
	if (nmoves == 0) {
		debug.Printf("Suicide!")
		return Left()
	}

	if (nmoves == 1) {
		debug.Printf("Select %s because it is the only viable move")
		return Result(moves[0].dir)
	}

	// TODO: at this point, we can choose to chase food, prefer a larger space to move into,
	// or aim to attack smaller snakes.  We'll opt to chase food now but this choice will
	// depend on our length relative to other snakes (esp. in a 2-snake end game) and on
	// our present health

	// Choose the move that makes best progress toward food
	var foodDist [3]int
	for mx := 0; mx < nmoves; mx++ {
		move := moves[mx]

		if s.IsFood(move.c) { 
			debug.Printf("Select %s because there is a food disc there")
			return Result(move.dir) 
		}

		foodDist[mx] = s.h+s.w
		for _,food := range s.food {
			mdist := ManDist(move.c,food.pos)
			if mdist < food.dist {
				foodDist[mx] = mdist
				break;
			}
		}
	}

	least := 0
	for mx := 1; mx < nmoves; mx++ {
		if foodDist[mx] < foodDist[least] { least = mx }
	}

	debug.Printf("Select %s because it makes the best progress toward food")
	return Result(moves[least].dir)
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
		HeadType: "bendr",
		TailType: "skinny",
	}

	mySnakes.Lock()
	mySnakes.m[request.You.ID] = colors[cx].name
	mySnakes.Unlock()

	fmt.Printf("INFO(%s): Start\n", colors[cx].name)
	
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(response)
}

// HandleEnd is called when a game your Battlesnake was playing has ended.
// It's purely for informational purposes, no response required.
func HandleEnd(w http.ResponseWriter, r *http.Request) {
	request := EndRequest{}
	json.NewDecoder(r.Body).Decode(&request)

	// TODO: clean up any context 

	// Nothing to respond with here
	fmt.Print("END\n")
}

func main() {
	port := os.Getenv("PORT")
	if len(port) == 0 {
		port = "8080"
	}

	mySnakes.m = make(map[string]string)

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
