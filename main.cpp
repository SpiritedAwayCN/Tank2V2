// Tank2 游戏样例程序
// 随机策略
// 作者：289371298 upgraded from zhouhy
// https://www.botzone.org.cn/games/Tank2

#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <cstring>
#include <queue>
#include <iomanip>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include "jsoncpp/json.h"
#endif

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;

struct Coordinate{
	int x, y;
};

namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif
	//这个是自写的
	const int next_step[4][2] = { {1,0},{-1,0},{0,1},{0,-1} };

	enum GameResult
	{
		NotFinished = -2,
		Draw = -1,
		Blue = 0,
		Red = 1
	};

	enum FieldItem
	{
		None = 0,
		Brick = 1,
		Steel = 2,
		Base = 4,
		Blue0 = 8,
		Blue1 = 16,
		Red0 = 32,
		Red1 = 64,
		Water = 128
	};

	template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
	template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
	template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
	template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
	template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
	template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
	template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

	enum Action
	{
		Invalid = -2,
		Stay = -1,
		Up, Right, Down, Left,
		UpShoot, RightShoot, DownShoot, LeftShoot
	};

	// 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
	// Side（对战双方） - 0 为蓝，1 为红
	// Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
	// Turn（回合编号） - 从 1 开始

	const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

	// 基地的横坐标
	const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

	// 基地的纵坐标
	const int baseY[sideCount] = { 0, fieldHeight - 1 };

	const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
	const FieldItem tankItemTypes[sideCount][tankPerSide] = {
		{ Blue0, Blue1 },{ Red0, Red1 }
	};

	int maxTurn = 100;

#ifdef _MSC_VER
#pragma endregion

#pragma region 工具函数和类
#endif

	inline bool ActionIsMove(Action x)
	{
		return x >= Up && x <= Left;
	}

	inline bool ActionIsShoot(Action x)
	{
		return x >= UpShoot && x <= LeftShoot;
	}

	inline bool ActionDirectionIsOpposite(Action a, Action b)
	{
		return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
	}

	inline bool CoordValid(int x, int y)
	{
		return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
	}

	// 判断 item 是不是叠在一起的多个坦克
	inline bool HasMultipleTank(FieldItem item)
	{
		// 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
		// 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
		return !!(item & (item - 1));
	}

	inline int GetTankSide(FieldItem item)
	{
		return item == Blue0 || item == Blue1 ? Blue : Red;
	}

	inline int GetTankID(FieldItem item)
	{
		return item == Blue0 || item == Red0 ? 0 : 1;
	}

	// 获得动作的方向
	inline int ExtractDirectionFromAction(Action x)
	{
		if (x >= Up)
			return x % 4;
		return -1;
	}

	// 物件消失的记录，用于回退
	struct DisappearLog
	{
		FieldItem item;

		// 导致其消失的回合的编号
		int turn;

		int x, y;
		bool operator< (const DisappearLog& b) const
		{
			if (x == b.x)
			{
				if (y == b.y)
					return item < b.item;
				return y < b.y;
			}
			return x < b.x;
		}
	};

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField 主要逻辑类
#endif

	class TankField
	{
	public:
		//!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

		// 游戏场地上的物件（一个格子上可能有多个坦克）
		FieldItem gameField[fieldHeight][fieldWidth] = {};

		// 坦克是否存活
		bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

		// 基地是否存活
		bool baseAlive[sideCount] = { true, true };

		// 坦克横坐标，-1表示坦克已炸
		int tankX[sideCount][tankPerSide] = {
			{ fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
		};

		// 坦克纵坐标，-1表示坦克已炸
		int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

		// 当前回合编号
		int currentTurn = 1;

		// 我是哪一方
		int mySide;

		// 用于回退的log
		stack<DisappearLog> logs;

		// 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
		Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

		//!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

		// 本回合双方即将执行的动作，需要手动填入
		Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

		// 判断行为是否合法（出界或移动到非空格子算作非法）
		// 未考虑坦克是否存活
		bool ActionIsValid(int side, int tank, Action act)
		{
			if (act == Invalid)
				return false;
			if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
				return false;
			if (act == Stay || act > Left)
				return true;
			int x = tankX[side][tank] + dx[act],
				y = tankY[side][tank] + dy[act];
			return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
		}

		// 判断 nextAction 中的所有行为是否都合法
		// 忽略掉未存活的坦克
		bool ActionIsValid()
		{
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
						return false;
			return true;
		}

	private:
		void _destroyTank(int side, int tank)
		{
			tankAlive[side][tank] = false;
			tankX[side][tank] = tankY[side][tank] = -1;
		}

		void _revertTank(int side, int tank, DisappearLog& log)
		{
			int &currX = tankX[side][tank], &currY = tankY[side][tank];
			if (tankAlive[side][tank])
				gameField[currY][currX] &= ~tankItemTypes[side][tank];
			else
				tankAlive[side][tank] = true;
			currX = log.x;
			currY = log.y;
			gameField[currY][currX] |= tankItemTypes[side][tank];
		}
	public:

		// 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
		bool DoAction()
		{
			if (!ActionIsValid())
				return false;

			// 1 移动
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];

					// 保存动作
					previousActions[currentTurn][side][tank] = act;
					if (tankAlive[side][tank] && ActionIsMove(act))
					{
						int &x = tankX[side][tank], &y = tankY[side][tank];
						FieldItem &items = gameField[y][x];

						// 记录 Log
						DisappearLog log;
						log.x = x;
						log.y = y;
						log.item = tankItemTypes[side][tank];
						log.turn = currentTurn;
						logs.push(log);

						// 变更坐标
						x += dx[act];
						y += dy[act];

						// 更换标记（注意格子可能有多个坦克）
						gameField[y][x] |= log.item;
						items &= ~log.item;
					}
				}

			// 2 射♂击!
			set<DisappearLog> itemsToBeDestroyed;
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];
					if (tankAlive[side][tank] && ActionIsShoot(act))
					{
						int dir = ExtractDirectionFromAction(act);
						int x = tankX[side][tank], y = tankY[side][tank];
						bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
						while (true)
						{
							x += dx[dir];
							y += dy[dir];
							if (!CoordValid(x, y))
								break;
							FieldItem items = gameField[y][x];
							//tank will not be on water, and water will not be shot, so it can be handled as None
							if (items != None && items != Water)
							{
								// 对射判断
								if (items >= Blue0 &&
									!hasMultipleTankWithMe && !HasMultipleTank(items))
								{
									// 自己这里和射到的目标格子都只有一个坦克
									Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
									if (ActionIsShoot(theirAction) &&
										ActionDirectionIsOpposite(act, theirAction))
									{
										// 而且我方和对方的射击方向是反的
										// 那么就忽视这次射击
										break;
									}
								}

								// 标记这些物件要被摧毁了（防止重复摧毁）
								for (int mask = 1; mask <= Red1; mask <<= 1)
									if (items & mask)
									{
										DisappearLog log;
										log.x = x;
										log.y = y;
										log.item = (FieldItem)mask;
										log.turn = currentTurn;
										itemsToBeDestroyed.insert(log);
									}
								break;
							}
						}
					}
				}

			for (auto& log : itemsToBeDestroyed)
			{
				switch (log.item)
				{
				case Base:
				{
					int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
					baseAlive[side] = false;
					break;
				}
				case Blue0:
					_destroyTank(Blue, 0);
					break;
				case Blue1:
					_destroyTank(Blue, 1);
					break;
				case Red0:
					_destroyTank(Red, 0);
					break;
				case Red1:
					_destroyTank(Red, 1);
					break;
				case Steel:
					continue;
				default:
					;
				}
				gameField[log.y][log.x] &= ~log.item;
				logs.push(log);
			}

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					nextAction[side][tank] = Invalid;

			currentTurn++;
			return true;
		}

		// 回到上一回合
		bool Revert()
		{
			if (currentTurn == 1)
				return false;

			currentTurn--;
			while (!logs.empty())
			{
				DisappearLog& log = logs.top();
				if (log.turn == currentTurn)
				{
					logs.pop();
					switch (log.item)
					{
					case Base:
					{
						int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
						baseAlive[side] = true;
						gameField[log.y][log.x] = Base;
						break;
					}
					case Brick:
						gameField[log.y][log.x] = Brick;
						break;
					case Blue0:
						_revertTank(Blue, 0, log);
						break;
					case Blue1:
						_revertTank(Blue, 1, log);
						break;
					case Red0:
						_revertTank(Red, 0, log);
						break;
					case Red1:
						_revertTank(Red, 1, log);
						break;
					default:
						;
					}
				}
				else
					break;
			}
			return true;
		}

		// 游戏是否结束？谁赢了？
		GameResult GetGameResult()
		{
			bool fail[sideCount] = {};
			for (int side = 0; side < sideCount; side++)
				if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
					fail[side] = true;
			if (fail[0] == fail[1])
				return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
			if (fail[Blue])
				return Red;
			return Blue;
		}

		/* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
		   initialize gameField[][]
		   brick>water>steel
		*/
		TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide)
		{
			for (int i = 0; i < 3; i++)
			{
				int mask = 1;
				for (int y = i * 3; y < (i + 1) * 3; y++)
				{
					for (int x = 0; x < fieldWidth; x++)
					{
						if (hasBrick[i] & mask)
							gameField[y][x] = Brick;
						else if (hasWater[i] & mask)
							gameField[y][x] = Water;
						else if (hasSteel[i] & mask)
							gameField[y][x] = Steel;
						mask <<= 1;
					}
				}
			}
			for (int side = 0; side < sideCount; side++)
			{
				for (int tank = 0; tank < tankPerSide; tank++)
					gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
				gameField[baseY[side]][baseX[side]] = Base;
			}
		}
		// 打印场地
		void DebugPrint()
		{
#ifndef _BOTZONE_ONLINE
			const string side2String[] = { "蓝", "红" };
			const string boolean2String[] = { "已炸", "存活" };
			const char* boldHR = "==============================";
			const char* slimHR = "------------------------------";
			cout << boldHR << endl
				<< "图例：" << endl
				<< ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
				<< "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
				<< slimHR << endl;
			for (int y = 0; y < fieldHeight; y++)
			{
				for (int x = 0; x < fieldWidth; x++)
				{
					switch (gameField[y][x])
					{
					case None:
						cout << '.';
						break;
					case Brick:
						cout << '#';
						break;
					case Steel:
						cout << '%';
						break;
					case Base:
						cout << '*';
						break;
					case Blue0:
						cout << 'b';
						break;
					case Blue1:
						cout << 'B';
						break;
					case Red0:
						cout << 'r';
						break;
					case Red1:
						cout << 'R';
						break;
					case Water:
						cout << 'W';
						break;
					default:
						cout << '@';
						break;
					}
				}
				cout << endl;
			}
			cout << slimHR << endl;
			for (int side = 0; side < sideCount; side++)
			{
				cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
				for (int tank = 0; tank < tankPerSide; tank++)
					cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
				cout << endl;
			}
			cout << "当前回合：" << currentTurn << "，";
			GameResult result = GetGameResult();
			if (result == -2)
				cout << "游戏尚未结束" << endl;
			else if (result == -1)
				cout << "游戏平局" << endl;
			else
				cout << side2String[result] << "方胜利" << endl;
			cout << boldHR << endl;
#endif
		}

		bool operator!= (const TankField& b) const
		{

			for (int y = 0; y < fieldHeight; y++)
				for (int x = 0; x < fieldWidth; x++)
					if (gameField[y][x] != b.gameField[y][x])
						return true;

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					if (tankX[side][tank] != b.tankX[side][tank])
						return true;
					if (tankY[side][tank] != b.tankY[side][tank])
						return true;
					if (tankAlive[side][tank] != b.tankAlive[side][tank])
						return true;
				}

			if (baseAlive[0] != b.baseAlive[0] ||
				baseAlive[1] != b.baseAlive[1])
				return true;

			if (currentTurn != b.currentTurn)
				return true;

			return false;
		}
	};

#ifdef _MSC_VER
#pragma endregion
#endif

	TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

	// 内部函数
	namespace Internals
	{
		Json::Reader reader;
#ifdef _BOTZONE_ONLINE
		Json::FastWriter writer;
#else
		Json::StyledWriter writer;
#endif

		void _processRequestOrResponse(Json::Value& value, bool isOpponent)
		{
			if (value.isArray())
			{
				if (!isOpponent)
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
				}
				else
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
					field->DoAction();
				}
			}
			else
			{
				// 是第一回合，裁判在介绍场地
				int hasBrick[3], hasWater[3], hasSteel[3];
				for (int i = 0; i < 3; i++) {//Tank2 feature(???????????????)
					hasWater[i] = value["waterfield"][i].asInt();
					hasBrick[i] = value["brickfield"][i].asInt();
					hasSteel[i] = value["steelfield"][i].asInt();
				}
				field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
			}
		}

		// 请使用 SubmitAndExit 或者 SubmitAndDontExit
		void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
		{
			Json::Value output(Json::objectValue), response(Json::arrayValue);
			response[0U] = tank0;
			response[1U] = tank1;
			output["response"] = response;
			if (!debug.empty())
				output["debug"] = debug;
			if (!data.empty())
				output["data"] = data;
			if (!globalData.empty())
				output["globalData"] = globalData;
			cout << writer.write(output) << endl;
		}
	}

	// 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
	// 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
	void ReadInput(istream& in, string& outData, string& outGlobalData)
	{
		Json::Value input;
		string inputString;
		do
		{
			getline(in, inputString);
		} while (inputString.empty());
#ifndef _BOTZONE_ONLINE
		// 猜测是单行还是多行
		char lastChar = inputString[inputString.size() - 1];
		if (lastChar != '}' && lastChar != ']')
		{
			// 第一行不以}或]结尾，猜测是多行
			string newString;
			do
			{
				getline(in, newString);
				inputString += newString;
			} while (newString != "}" && newString != "]");
		}
#endif
		Internals::reader.parse(inputString, input);

		if (input.isObject())
		{
			Json::Value requests = input["requests"], responses = input["responses"];
			if (!requests.isNull() && requests.isArray())
			{
				size_t i, n = requests.size();
				for (i = 0; i < n; i++)
				{
					Internals::_processRequestOrResponse(requests[i], true);
					if (i < n - 1)
						Internals::_processRequestOrResponse(responses[i], false);
				}
				outData = input["data"].asString();
				outGlobalData = input["globaldata"].asString();
				return;
			}
		}
		Internals::_processRequestOrResponse(input, true);
	}

	// 提交决策并退出，下回合时会重新运行程序
	void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globalData = "")
	{
		Internals::_submitAction(tank0, tank1, debug, data, globalData);
		exit(0); //sca注：此处可设置断点
	}

	// 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
	// 如果游戏结束，程序会被系统杀死
	void SubmitAndDontExit(Action tank0, Action tank1)
	{
		Internals::_submitAction(tank0, tank1);
		field->nextAction[field->mySide][0] = tank0;
		field->nextAction[field->mySide][1] = tank1;
		cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
	}

	//以下是自写部分

	//概率相加，应该看得懂意思
	inline void AddProbability(double& P, double value) {
		P = 1 - (1 - P)*(1 - value);
	}

	//是否可行走（空地或坦克，第二个参数设置为true则不能通过坦克
	inline bool ItemIsAccessible(const FieldItem item, bool IgnoreTank = true) {
		if (item == None) return true;
		if (item == Blue0 || item == Red0 || item == Blue1 || item == Red1) return IgnoreTank;
		return false;
	}

	//是否可通过子弹
	inline bool CanBulletAcross(const FieldItem item, bool IgnoreTank = true) {
		if (item == None || item == Water) return true;
		if (item == Blue0 || item == Red0 || item == Blue1 || item == Red1) return IgnoreTank;
		return false;
	}

	//判断方的Tank_id号坦克（或者传Fielditem）是否在某个tank的射程内，返回对方坦克的id
	inline int IsInShotRange(int Tank_id, int side = field->mySide) {
		//晚点写 @谢宇飞

		return -1; //不在任何Tank的射程内，返回-1
	}


	int my_action[tankPerSide] = { -2, -2 };
	int min_step_to_base[sideCount][fieldHeight][fieldWidth];
	double shot_range[sideCount][fieldHeight][fieldWidth]; //希望这个数组存的是类似于概率的数组，表示接下来的几步内某个进入某方射程的概率
	queue<Coordinate> BFS_generate_queue;

	inline double GetRandom() {
		return (rand() % 10000)*1.0 / 10000;
	}

	inline bool IsTank(FieldItem item) {
		return item >= Blue0 && item < Water;
	}

	inline Action Get_My_Action(int my_dir, bool shoot) {
		//mydir 0123->下上右左  官方 0123->上右下左
		if (my_dir < 0) return Action(my_dir);
		int number = (my_dir == 3 ? 3 : (my_dir + 2) % 3);
		if (shoot) number += 4;
		return Action(number);
	}

	//获取(x,y)处朝某方向射出的子弹打到的第一个目标
	inline FieldItem Get_Shot_Item(int x, int y, int dir) {
		
		if (my_action[0] >= 0 && my_action[0] <= 3) {

		}
	}

	//入队处理，仅限初始化最小数组时调用
	inline void push_BFS_queue(int x, int y, int step, int side) {
		if (!CoordValid(x, y)) return;
		if (field->gameField[x][y] != Brick && !ItemIsAccessible(field->gameField[x][y])) return;
		int temp = step;
		temp += field->gameField[x][y] == Brick ? 2 : 1;  //砖块则步数+2 否则+1
		if (min_step_to_base[side][x][y] > temp || min_step_to_base[side][x][y] < 0) {
			BFS_generate_queue.push(Coordinate{ x,y });
			min_step_to_base[side][x][y] = temp;
		}
	}
	//生成到终点的最小步数
	void genarate_min_step(int side) {
		while (!BFS_generate_queue.empty()) BFS_generate_queue.pop(); //清空队列
		memset(min_step_to_base[side], -1, sizeof(min_step_to_base[side])); //全部设为-1，表示还没有找
		min_step_to_base[side][baseY[side ^ 1]][baseX[side ^ 1]] = 0; //对方基地处是0步
		BFS_generate_queue.push(Coordinate{ baseY[side ^ 1],baseX[side ^ 1] });
		int i = 0, j = 0;
		for (i = baseY[side ^ 1] - 1; i >= 0 && ItemIsAccessible(field->gameField[i][baseX[side ^ 1]]); i--) {
			min_step_to_base[side][i][baseX[side ^ 1]] = 1; //正上方所有与对方基地间无墙的距离是1
			BFS_generate_queue.push(Coordinate{ i,baseX[side ^ 1] });
		}
		/*
		if (i >= 0 && field->gameField[i][baseX[side ^ 1]] == Brick) {
			min_step_to_base[side][i][baseX[side ^ 1]] = 2; //正上方第一个可击碎的墙离终点的距离是2
			BFS_generate_queue.push(Coordinate{ i,baseX[side ^ 1] });
		}
		*/
		for (i = baseY[side ^ 1] + 1; i < fieldHeight && ItemIsAccessible(field->gameField[i][baseX[side ^ 1]]); i++) {
			min_step_to_base[side][i][baseX[side ^ 1]] = 1; //正下方所有与对方基地间无墙的距离是1
			BFS_generate_queue.push(Coordinate{ i,baseX[side ^ 1] });
		}

		for (j = baseX[side ^ 1] - 1; j >= 0 && ItemIsAccessible(field->gameField[baseY[side ^ 1]][j]); j--) {
			min_step_to_base[side][baseY[side ^ 1]][j] = 1; //正左方所有与对方基地间无墙的距离是1
			BFS_generate_queue.push(Coordinate{ baseY[side ^ 1], j });
		}

		for (j = baseX[side ^ 1] + 1; j < fieldWidth && ItemIsAccessible(field->gameField[baseY[side ^ 1]][j]); j++) {
			min_step_to_base[side][baseY[side ^ 1]][j] = 1; //正右方所有与对方基地间无墙的距离是1
			BFS_generate_queue.push(Coordinate{ baseY[side ^ 1], j });
		}
		//下面开始BFS
		while (!BFS_generate_queue.empty()) {
			int cx = BFS_generate_queue.front().x, cy = BFS_generate_queue.front().y;
			BFS_generate_queue.pop();
			push_BFS_queue(cx - 1, cy, min_step_to_base[side][cx][cy], side);
			push_BFS_queue(cx + 1, cy, min_step_to_base[side][cx][cy], side);
			push_BFS_queue(cx, cy - 1, min_step_to_base[side][cx][cy], side);
			push_BFS_queue(cx, cy + 1, min_step_to_base[side][cx][cy], side);
		}
		return;
	}
	//生成各个位置进入射程的概率数组（目前是傻瓜版）
	void generate_shot_range(int side) {
		memset(shot_range[side], 0, sizeof(shot_range[side]));
		for (int id = 0; id < tankPerSide; id++) {
			if (!field->tankAlive[side][id]) continue;
			int tx = field->tankY[side][id], ty = field->tankX[side][id]; //随时注意X Y方向与一般的不一样
			for (int i = tx - 1; i >= 0 && CanBulletAcross(field->gameField[i][ty]); i--) {
				AddProbability(shot_range[side][i][ty], 0.4 * (side == 0 ? 0.1 : 1)); //参数0.9可调 side为0是向下进攻，向上发射子弹概率少一些
			}
			for (int i = tx + 1; i <fieldHeight && CanBulletAcross(field->gameField[i][ty]); i++) {
				AddProbability(shot_range[side][i][ty], 0.4 * (side == 1 ? 0.1 : 1)); //以后最好额外定义概率数组，不然每次一大堆数据不好调参
			}
			for (int j = ty - 1; j >= 0 && CanBulletAcross(field->gameField[tx][j]); j--) {
				AddProbability(shot_range[side][tx][j], 0.27);
			}
			for (int j = ty + 1; j < fieldWidth && CanBulletAcross(field->gameField[tx][j]); j++) {
				AddProbability(shot_range[side][tx][j], 0.27);
			}
			//概率：前 0.4 左/右 0.27 后0.04
			//可修改为计算n步之后的概率，以后改 @李辰剑
		}
		return;
	}

	//基于最短路的傻瓜策略
	int get_stupid_action(int tank_id) {
		bool force_move_mode = false;
		int side = field->mySide;

		if (!field->tankAlive[side][tank_id]) return my_action[tank_id] = -1; //坦克已死，没你的事了

		int tx = field->tankY[side][tank_id], ty = field->tankX[side][tank_id]; //当前tank坐标
		int fx = field->tankY[side][tank_id ^1], fy = field->tankX[side][tank_id^1]; //另一个友方tank坐标
		if (my_action[tank_id ^ 1] >= 0 && my_action[tank_id ^ 1] <= 3) {
			fx += next_step[my_action[tank_id ^ 1]][0];
			fy += next_step[my_action[tank_id ^ 1]][1];
		}

		if (field->previousActions[field->currentTurn - 1][side][tank_id] > Left) force_move_mode = true; //上一步是射子弹

		//↓一下可射到基地的特判
		if (min_step_to_base[side][tx][ty] == 1) {
			if (!force_move_mode) {
				if (baseX[side ^ 1] == ty) { my_action[tank_id] = side + 4;} //同一竖行，则向前射
				else { my_action[tank_id] = 4 + (baseX[side ^ 1] < ty ? 3 : 2); } //同一横行，则向基地射
			}
			else {
				int ans = -1;//默认不动
				double risk = shot_range[side ^ 1][tx][ty]; //选取为1且射中风险最小的位置
				int gx, gy;
				for (int dir = 0; dir < 4; dir++) {
					gx = tx + next_step[dir][0];
					gy = ty + next_step[dir][1];
					if (!CoordValid(gx, gy)) continue;
					if (ItemIsAccessible(field->gameField[gx][gy], true)) {
						double temp = shot_range[side ^ 1][gx][gy];
						temp += (min_step_to_base[side][gx][gy] - 0.9)*GetRandom(); //1的风险系数比2小很多
						if (risk > shot_range[side ^ 1][gx][gy]) {
							risk = shot_range[side ^ 1][gx][gy];
							ans = dir;
						}
						else if (risk == temp && GetRandom()<0.5) {
							ans = dir; //两个风险一致，则有0.5的概率换方向移动
						}
					}
				}
				my_action[tank_id] = ans;
			}
			return my_action[tank_id];
		}


		//0下 1上 2右 3左  权重
		double act[4] = { -1,-1,-1,-1};
		for (int i = 0; i < 4; i++) {
			int gx = tx + next_step[i][0], gy = ty + next_step[i][1];
			if (!CoordValid(gx, gy)) continue;
			if (min_step_to_base[side][tx][ty] >= min_step_to_base[side][gx][gy] - 1 && min_step_to_base[side][gx][gy]>=0) {
				act[i] = min_step_to_base[side][tx][ty] - min_step_to_base[side][gx][gy] + 0.3;
				if (field->gameField[gx][gy] == Brick && force_move_mode) act[i] = -1.8;
			}
			act[i] += 0.8;
		}
		//↑先把合法的弄成非负

		//概率随机，若当前位置在射程内会强制进入move模式
		if (GetRandom() <= shot_range[side ^ 1][tx][ty] * 0.7) force_move_mode = true;
		else if (!force_move_mode && GetRandom() <= 0.6) {
			int ans = -1;
			// 不要怂 直接刚 看看是哪个方向
			for (int dir = 0; dir < 4; dir++) {
				for (int ii = tx, jj = ty; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]) {
					if (fx == ii && fy == jj)break; //停火，友军！
					if (IsTank(field->gameField[ii][jj]) && GetTankSide(field->gameField[ii][jj]) != side) {ans = dir; break;} //敌军，上！
				}
				if (ans >= 0) break;
			}
			if (ans >= 0) { my_action[tank_id] = ans + 4; return my_action[tank_id]; }
		}
		double shot_weight[4] = { 0,0,0,0 }; //shoot与move的权重
		bool skip_loop;
		if (!force_move_mode) {
			//分配权重 这个方向是射还是走
			for (int dir = 0; dir < 4; dir++) {
				skip_loop = false;
				int ii = tx + next_step[dir][0], jj = ty + next_step[dir][1], cnt = 0;
				for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]) {
					if (fx == ii && fy == jj) {
						skip_loop = true;
						break;
					}
					cnt++;
				}
				if (skip_loop || !CoordValid(ii, jj)) continue; //停火，友军！
				if (field->gameField[ii][jj] == Brick) {
					//此时射击才有意义
					shot_weight[dir] += 0.6;
					shot_weight[dir] += shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]] * 0.8;
					if (cnt + min_step_to_base[side][ii][jj] > min_step_to_base[side][tx][ty]) {
						//被射的点不在最短路上
						shot_weight[dir] /= 2 + (cnt + min_step_to_base[side][ii][jj] - min_step_to_base[side][tx][ty])*GetRandom();
					}
				}
				//注意：没考虑射出后对位
				
				if ((side == 0 && ii < fieldHeight / 2) || (side == 1 && ii > fieldHeight / 2))shot_weight[dir] *= 0.92; //己方半场射击概率更低 
				else shot_weight[dir] *= 1.08; //对方半场的射率更高
				while (--cnt > 0) shot_weight[dir] *= 0.87; //墙每远一格 概率减小一定倍数
			}
			shot_weight[side] *= 1.2; //前
			shot_weight[side ^ 1] *= 0.8; //后
		}
		//act[dir]<0不考虑 shot_weight==0不考虑
		for (int dir = 0; dir < 4; dir++) {
			if (GetRandom() < shot_weight[dir] || !ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false))
				act[dir] = act[dir] / 2+ shot_weight[dir], shot_weight[dir] = 2;//=2(>1)作为标记供以后判断是移还是射(别中了射击)
			else if(ActionIsMove(field->previousActions[field->currentTurn - 1][side][tank_id])
				&& ActionDirectionIsOpposite(field->previousActions[field->currentTurn - 1][side][tank_id], Get_My_Action(dir, false))) {
				//若是移动回上一步
				act[dir] /= 5 + GetRandom() * 4;
			}
			if (min_step_to_base[side][tx + next_step[dir][0]] [ty + next_step[dir][1]] > min_step_to_base[side][tx][ty]) {
				act[dir] /= 2 + GetRandom() * 2;
			}
			if (act[dir] < 0) act[dir] = 0;
		}
		double sum = 0;
		//归一化&前缀和
		for (int i = 0; i < 4; i++)sum += act[i];
		for (int i = 0; i < 4; i++) { 
			act[i] /= sum;
			if (i > 0) act[i] += act[i - 1];
		}
		sum = GetRandom();
		int ans = -1;
		for (ans = 0; act[ans] < sum; ans++);
		my_action[tank_id] = ans;
		if (shot_weight[ans] > 1.5) my_action[tank_id] += 4; //若别中的是设计，则方案+4
		return my_action[tank_id];

	}
	void Debug_Print_MinStep() {
#ifndef _BOTZONE_ONLINE
		for (int side = 0; side < 2; side++) {
			cout << "###side = " << side << "###\n";
			for (int i = 0; i < fieldHeight; i++) {
				for (int j = 0; j < fieldWidth; j++) {
					cout << std::setw(2) <<min_step_to_base[side][i][j] <<' ';
				}
				cout << endl;
			}
			cout << endl;
		}
		cout << "===========Shoot Range===========\n";
		for (int side = 0; side < 2; side++) {
			cout << "###side = " << side << "###\n";
			for (int i = 0; i < fieldHeight; i++) {
				for (int j = 0; j < fieldWidth; j++) {
					cout << std::setprecision(3) << shot_range[side][i][j] << ' ';
				}
				cout << endl;
			}
			cout << endl;
		}
#endif
	}

#ifdef _MSC_VER
#pragma endregion
#endif
}
int RandBetween(int from, int to)
{
	return rand() % (to - from) + from;
}

TankGame::Action RandAction(int tank)
{
	while (true)
	{
		auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
		if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
			return act;
	}
}


int main()
{
	srand((unsigned)time(nullptr));

	string data, globaldata;
	TankGame::ReadInput(cin, data, globaldata);
	TankGame::field->DebugPrint();
	TankGame::genarate_min_step(0);
	TankGame::genarate_min_step(1);
	TankGame::generate_shot_range(0);
	TankGame::generate_shot_range(1);
	TankGame::Debug_Print_MinStep();

	TankGame::get_stupid_action(0);
	TankGame::get_stupid_action(1);
	TankGame::Action act0 = TankGame::Get_My_Action(TankGame::my_action[0] % 4, TankGame::my_action[0] >= 4);
	TankGame::Action act1 = TankGame::Get_My_Action(TankGame::my_action[1] % 4, TankGame::my_action[1] >= 4);
	int side = TankGame::field->mySide;

	//防错处理，若生成的策略无效则：
	if (!TankGame::field->ActionIsValid(side, 0, act0)) {
		act0 = RandAction(0);
		if (TankGame::GetRandom() < 0.65) act0 = TankGame::Stay;
	}
	if (!TankGame::field->ActionIsValid(side, 1, act1)) {
		act1 = RandAction(1);
		if (TankGame::GetRandom() < 0.65) act1 = TankGame::Stay;
	}

	TankGame::SubmitAndExit(act0, act1);
}