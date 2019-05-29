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
#include <algorithm>
#include <sstream>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include "jsoncpp/json.h"
#endif

using std::runtime_error;
using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;
using std::vector;
using std::pair;
using std::make_pair;
using std::min;
using std::max;
using std::stringstream;
//这个是自写的
const int next_step[4][2] = { {1,0},{-1,0},{0,1},{0,-1} };

namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

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

		inline bool inOppositeHalf(int tank_id,int side, bool default_value = true) {
			if (!tankAlive[side][tank_id]) return default_value;
			if (side)
				return tankY[side][tank_id] <= 4;
			else
				return tankY[side][tank_id] >= 4;
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
	struct Coordinate {
		int x, y;
		void Rev(TankGame::Action act) {
			switch (act) {
			case TankGame::Up :
				x += 1;
				break;
			case TankGame::Down :
				x -= 1;
				break;
			case TankGame::Right :
				y -= 1;
				break;
			case TankGame::Left :
				y += 1;
				break;
			}
		}
		bool operator!=(Coordinate& B) {
			return B.x != x || B.y != y;
		}
	};
	//概率相加，应该看得懂意思
	inline void AddProbability(double& P, double value) {
		P = 1 - (1 - P)*(1 - value);
	}

	//是否可行走（空地或坦克，第二个参数设置为true则不能通过坦克
	inline bool ItemIsAccessible(const FieldItem item, bool IgnoreTank = true) {
		if (item == None) return true;
		if (HasMultipleTank(item)) return true;
		if (item == Blue0 || item == Red0 || item == Blue1 || item == Red1) return IgnoreTank;
		return false;
	}

	//是否可通过子弹
	inline bool CanBulletAcross(const FieldItem item, bool IgnoreTank = true, int IgnoreSide = -1) {
		if (item == None || item == Water) return true;
		if (IgnoreTank &&  HasMultipleTank(item)) return true;
		if (item == Blue0 || item == Blue1) return IgnoreTank || IgnoreSide == 0;
		if (item == Red0 || item == Red1) return IgnoreTank || IgnoreSide == 1;
		return false;
	}



	int my_action[tankPerSide] = { -2, -2 };
	int min_step_to_base[sideCount][fieldHeight][fieldWidth];
	int min_path[sideCount][tankPerSide][fieldHeight][fieldWidth];
	double shot_range[sideCount][fieldHeight][fieldWidth], real_shot_range[sideCount][fieldHeight][fieldWidth]; 
	//希望这个数组存的是类似于概率的数组，表示接下来的几步内某个进入某方射程的概率
	queue<Coordinate> BFS_generate_queue;

	inline double GetRandom() {
		return (rand() % 10000)*1.0 / 10000;
	}

	inline bool IsTank(FieldItem item, bool IgnoreMulty = true) {
		if (!IgnoreMulty && HasMultipleTank(item)) return true;
		return item == Blue0 || item==Red0 || item==Blue1 || item==Red1;
	}

	inline Action Get_My_Action(int my_dir, bool shoot) {
		//mydir 0123->下上右左  官方 0123->上右下左
		if (my_dir < 0) return Action(my_dir);
		int number = (my_dir == 3 ? 3 : (my_dir + 2) % 3);
		if (shoot) number += 4;
		return Action(number);
	}

	inline bool shoot_friend(int side,int tank_id,int fx, int fy) {
		if (my_action[tank_id] < 4) return false;
		int dir = my_action[tank_id] - 4;
		for (int ii = field->tankY[side][tank_id], jj = field->tankX[side][tank_id]; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]);
			ii += next_step[dir][0], jj += next_step[dir][1]) {
			if (fx == ii && fy == jj) return true;
		}
		return false;
	}

	inline Coordinate shoot_coord(int dir, int sx, int sy) {
		int ii, jj;
		for (ii = sx, jj = sy; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]);
			ii += next_step[dir][0], jj += next_step[dir][1]) {
			if (field->gameField[ii][jj] == Brick) break;
		}
		return Coordinate{ ii,jj };
	}

	//判断(x,y)是否在(tx,ty)这个坦克的射程内
	inline bool InShootRange(int tx,int ty, int x, int y, bool IgnoreTank = true, int IgnoreSide = -1) {
		int l, r;
		if (tx == x) {
			l = std::min(ty, y);
			r = std::max(ty, y);
			for (int i = l + 1; i < r; i++) {
				if (!CoordValid(tx, i)) continue;
				if (!CanBulletAcross(field->gameField[tx][i],IgnoreTank, IgnoreSide)) return false;
			}
			return true;
		}
		else if (ty == y) {
			l = std::min(tx, x);
			r = std::max(tx, x);
			for (int i = l + 1; i < r; i++) {
				if (!CoordValid(i, ty)) continue;
				if (!CanBulletAcross(field->gameField[i][ty], IgnoreTank, IgnoreSide)) return false;
			}
			return true;
		}
		return false;
	}

	//判断当前位置是不是有唯一的最短路下降方向，若有则返回方向，否则返回-1
	inline int IsUniqueDir(int side, int tx,int ty) {
		int ans = -1;
		for (int dir = 0; dir < 4; dir++) {
			if (!CoordValid(tx + next_step[dir][0], ty + next_step[dir][1])) continue;
			if (!ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false)) continue;
			if (min_step_to_base[side][tx][ty] > min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
				if (ans == -1) ans = dir;
				else return -1;
			}
		}
		return ans;
	}
	//返回标准版
	bool has_tank(int, int);
	bool has_unique_dsc_dir(int side, int x, int y)
	{
		int tx, ty;
		int numDscDir = 0;
		int best_delta = 0;
		for (int dir = 0; dir < 4; dir++)
		{
			tx = x + dx[dir];
			ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			if (field->gameField[ty][tx] == Steel || field->gameField[ty][tx] == Water || 
				field->gameField[ty][tx] == Base || has_tank(tx,ty))
				continue;
			int delta = min_step_to_base[side][y][x] - min_step_to_base[side][ty][tx];
			if (delta > best_delta)
			{
				numDscDir = 1;
				best_delta = delta;
			}
			else if (delta == best_delta)
				numDscDir++;
		}
		
		return numDscDir == 1;
	}
	int get_unique_dsc_dir(int side, int x, int y)
	{
		int tx, ty;
		int best_delta = 0;
		int best_dir = -1;
		for (int dir = 0; dir < 4; dir++)
		{
			tx = x + dx[dir];
			ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			if (field->gameField[ty][tx] == Steel || field->gameField[ty][tx] == Water || 
				field->gameField[ty][tx] == Base || has_tank(tx, ty))
				continue;

			int delta = min_step_to_base[side][y][x] - min_step_to_base[side][ty][tx];
			if (delta > best_delta)
			{
				best_dir = dir;
				best_delta = delta;
			}
		}
		if (best_dir != -1)
			return best_dir;
		return -1;
	}
	inline bool is_none(int x, int y)
	{
		return field->gameField[y][x] == None;
	}
	//队友坦克则搜索时权重+2
	constexpr int tank_weight = 3;


	inline void Friend_Weight(int side, int x, int y, int* num = NULL) {
		FieldItem item = field->gameField[x][y];
		if (!num) num = &min_step_to_base[side][x][y];
		if (HasMultipleTank(item)) {
			if (x == field->tankY[side][0] && y == field->tankX[side][0]) *num += tank_weight;
			if (x == field->tankY[side][1] && y == field->tankX[side][1]) *num += tank_weight; //队友重合则+4
		}
		else if (IsTank(item) && GetTankSide(item) == side && field->tankAlive[side][GetTankID(item)])
			*num += tank_weight;
	}
	//入队处理，仅限初始化最小数组时调用
	inline void push_BFS_queue(int x, int y, int step, int side) {
		if (!CoordValid(x, y)) return;
		if (field->gameField[x][y] != Brick && !ItemIsAccessible(field->gameField[x][y])) return;
		int temp = step;
		temp += field->gameField[x][y] == Brick ? 2 : 1;  //砖块则步数+2 否则+1
		Friend_Weight(side, x, y, &temp);
		if (abs(x - baseY[side]) + abs(y - baseX[side]) <= 1 && field->gameField[x][y] == Brick) temp += 1;
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
		
		int value = 1;
		for (i = baseY[side ^ 1] - 1; i >= 0 &&(ItemIsAccessible(field->gameField[i][baseX[side ^ 1]])||field->gameField[i][baseX[side ^ 1]] == Brick); i--) {
			if (field->gameField[i][baseX[side ^ 1]] == Brick) value += 2;
			min_step_to_base[side][i][baseX[side ^ 1]] = value; //正上方所有与对方基地间无墙的距离是1
			Friend_Weight(side, i, baseX[side ^ 1]);
			BFS_generate_queue.push(Coordinate{ i,baseX[side ^ 1] });
		}
		value = 1;
		for (i = baseY[side ^ 1] + 1; i < fieldHeight && (ItemIsAccessible(field->gameField[i][baseX[side ^ 1]]) || field->gameField[i][baseX[side ^ 1]] == Brick); i++) {
			if (field->gameField[i][baseX[side ^ 1]] == Brick) value += 2;
			min_step_to_base[side][i][baseX[side ^ 1]] = value; //正下方所有与对方基地间无墙的距离是1
			Friend_Weight(side, i, baseX[side ^ 1]);
			BFS_generate_queue.push(Coordinate{ i,baseX[side ^ 1] });
		}
		bool left_half = false, right_half = false;
		for (int i = 0; i < 3; i++) {
			for (int j = 0; j < 3; j++) {
				if (IsTank(field->gameField[i + 6 * (1 - side)][j]) && GetTankSide(field->gameField[i + 6 * (1 - side)][j]) != side) {
					left_half = true;
					break;
				} //左半边靠近对方基地的1/4区域内有地方坦克
			}
			if (left_half)break;
		}
		for (int i = 0; i < 3; i++) {
			for (int j = 6; j < 9; j++) {
				if (IsTank(field->gameField[i + 6 * (1 - side)][j]) && GetTankSide(field->gameField[i + 6 * (1 - side)][j]) != side) {
					right_half = true;
					break;
				} //右半边靠近对方基地的1/4区域内有地方坦克
			}
			if (right_half)break;
		}
		if (field->currentTurn > 3) {
			left_half = right_half = false;
			//不再调用错误的BFS
		}
		//left_half = false, right_half = false;
		value = 1;
		for (j = baseX[side ^ 1] - 1; j >= 0 && (ItemIsAccessible(field->gameField[baseY[side ^ 1]][j]) || field->gameField[baseY[side ^ 1]][j]==Brick); j--) {
			if (field->gameField[baseY[side ^ 1]][j] == Brick) {
				if (left_half) break;
				value += 2;
			}
			min_step_to_base[side][baseY[side ^ 1]][j] = value/* + (value==1 && left_half ? 1 : 0)*/; //正左方所有与对方基地间无墙的距离是1
			Friend_Weight(side, baseY[side ^ 1], j);
			BFS_generate_queue.push(Coordinate{ baseY[side ^ 1], j });
		}
		value = 1;
		for (j = baseX[side ^ 1] + 1; j < fieldWidth && (ItemIsAccessible(field->gameField[baseY[side ^ 1]][j]) || field->gameField[baseY[side ^ 1]][j] == Brick); j++) {
			if (field->gameField[baseY[side ^ 1]][j] == Brick) {
				if (right_half) break;
				value += 2;
			}
			min_step_to_base[side][baseY[side ^ 1]][j] = value/* + (value==1 && right_half ? 1 : 0)*/; //正右方所有与对方基地间无墙的距离是1
			Friend_Weight(side, baseY[side ^ 1], j);
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
		if(field->tankAlive[side][0])min_step_to_base[side][field->tankY[side][0]][field->tankX[side][0]] -= tank_weight;
		if(field->tankAlive[side][1])min_step_to_base[side][field->tankY[side][1]][field->tankX[side][1]] -= tank_weight;
		return;
	}

	//by lcj
	//由之前生成的 min_step_to_base数组 生成每方每个坦克的最短路路径
	//注意：xy约定与sca不同
	//dfs辅助函数
	void _genetrate_min_path_dfs(const int& side,const int& tank,int x0,int y0, vector<pair<int, int>>& prev_path)
	{
		bool terminate = true;
		if (!field->tankAlive[side][tank]) return;

		for (int i = 0; i < 4; i++)//环顾四周找梯度下降方向，那就是最短路的下一步
		{
			int x1 = x0 + dx[i];
			int y1 = y0 + dy[i];

			//如果坐标到了战场外面，跳过
			if (!CoordValid(x1, y1)) continue;
			//如果遇到了钢板/水域，跳过
			if (min_step_to_base[side][y1][x1] == -1) continue;
			//else
			//如果梯度下降，那么(x1,y1)就是最短路的下一步
			if (min_step_to_base[side][y1][x1] < min_step_to_base[side][y0][x0])	
			{
				terminate = false;
				prev_path.push_back(make_pair(y1, x1));
				_genetrate_min_path_dfs(side, tank, x1,y1, prev_path);//CORE RECURSION
				prev_path.pop_back();
			}
		}
		
		if (terminate)//递归终点（不只是基地！而是任何距离下降的终点，ie，前后左右找不到距离下降的地方了
		{
			for (auto p : prev_path)
			{
				int x = p.second;
				int y = p.first;
				min_path[side][tank][y][x] += 1;
			}
			//特殊情况：如果四周都没有梯度下降的方向，那应该是已经到了和敌方基地同一条线上，
			//不用走，直接射击也可以获胜
			//这时，把这个点到基地都标记上最短路
			int enemySide = ((side == Red) ? Blue : Red);
			for (int y = min(y0, baseY[enemySide]); y <= max(y0, baseY[enemySide]); y++)
				for (int x = min(x0, baseX[enemySide]); x <= max(x0, baseX[enemySide]); x++)
					min_path[side][tank][y][x] += 1;
			//最后，(x0,y0)和敌方基地上多加1，减去
			min_path[side][tank][y0][x0] -= 1;
			min_path[side][tank][baseY[enemySide]][baseX[enemySide]] -= 1;
			return;
		}
	}
	void generate_min_path()
	{
		memset(min_path, 0, sizeof(min_path));
		for (int side = 0; side < sideCount; side++)//perSide
		{
			for (int tank = 0; tank < tankPerSide; tank++)//perTank
			{
				//此坦克当前坐标
				int tx = field->tankX[side][tank];
				int ty = field->tankY[side][tank];

				vector<pair<int, int>> prev_path;
				_genetrate_min_path_dfs(side, tank, tx, ty, prev_path);

			
				//debug breakpoint
				2 + 2 == 5;
			}
		}
	}
	//生成各个位置进入射程的概率数组（目前是傻瓜版）
	void generate_shot_range(int side , bool IgnoreFeasible = true) {
		if (IgnoreFeasible) {
			memset(shot_range[side], 0, sizeof(shot_range[side]));

			for (int id = 0; id < tankPerSide; id++) {
				if (!field->tankAlive[side][id]) continue;
				int tx = field->tankY[side][id], ty = field->tankX[side][id], i, j; //随时注意X Y方向与一般的不一样
				for (i = tx - 1; i >= 0 && CanBulletAcross(field->gameField[i][ty]); i--) {
					AddProbability(shot_range[side][i][ty], 0.4 * (side == 0 ? 0.1 : 1)); //参数0.9可调 side为0是向下进攻，向上发射子弹概率少一些
				}
				if (i >= 0)AddProbability(shot_range[side][i][ty], 0.4 * (side == 0 ? 0.1 : 1));
				for (i = tx + 1; i < fieldHeight && CanBulletAcross(field->gameField[i][ty]); i++) {
					AddProbability(shot_range[side][i][ty], 0.4 * (side == 1 ? 0.1 : 1)); //以后最好额外定义概率数组，不然每次一大堆数据不好调参
				}
				if (i < fieldHeight) AddProbability(shot_range[side][i][ty], 0.4 * (side == 1 ? 0.1 : 1));
				for (j = ty - 1; j >= 0 && CanBulletAcross(field->gameField[tx][j]); j--) {
					AddProbability(shot_range[side][tx][j], 0.27);
				}
				if (j >= 0) AddProbability(shot_range[side][tx][j], 0.27);
				for (j = ty + 1; j < fieldWidth && CanBulletAcross(field->gameField[tx][j]); j++) {
					AddProbability(shot_range[side][tx][j], 0.27);
				}
				if (j < fieldHeight)AddProbability(shot_range[side][tx][j], 0.27);
				//概率：前 0.4 左/右 0.27 后0.04
				//可修改为计算n步之后的概率，以后改 @李辰剑
			}
		}
		else {
			memset(real_shot_range[side], 0, sizeof(real_shot_range[side]));

			for (int id = 0; id < tankPerSide; id++) {
				if (!field->tankAlive[side][id]) continue;
				if (field->previousActions[field->currentTurn - 1][side][id] > Left) continue;
				int tx = field->tankY[side][id], ty = field->tankX[side][id], i, j; //随时注意X Y方向与一般的不一样
				for (i = tx - 1; i >= 0 && CanBulletAcross(field->gameField[i][ty]); i--) {
					AddProbability(real_shot_range[side][i][ty], 0.4 * (side == 0 ? 0.1 : 1)); //参数0.9可调 side为0是向下进攻，向上发射子弹概率少一些
				}
				if (i >= 0)AddProbability(real_shot_range[side][i][ty], 0.4 * (side == 0 ? 0.1 : 1));
				for (i = tx + 1; i < fieldHeight && CanBulletAcross(field->gameField[i][ty]); i++) {
					AddProbability(real_shot_range[side][i][ty], 0.4 * (side == 1 ? 0.1 : 1)); //以后最好额外定义概率数组，不然每次一大堆数据不好调参
				}
				if (i < fieldHeight) AddProbability(real_shot_range[side][i][ty], 0.4 * (side == 1 ? 0.1 : 1));
				for (j = ty - 1; j >= 0 && CanBulletAcross(field->gameField[tx][j]); j--) {
					AddProbability(real_shot_range[side][tx][j], 0.27);
				}
				if (j >= 0) AddProbability(real_shot_range[side][tx][j], 0.27);
				for (j = ty + 1; j < fieldWidth && CanBulletAcross(field->gameField[tx][j]); j++) {
					AddProbability(real_shot_range[side][tx][j], 0.27);
				}
				if (j < fieldHeight)AddProbability(real_shot_range[side][tx][j], 0.27);
				//概率：前 0.4 左/右 0.27 后0.04
				//可修改为计算n步之后的概率，以后改 @李辰剑
			}
		}
		
		return;
	}
	int temp_action[tankPerSide] = { Stay,Stay };
	void Debug_Print_MinStep();

	//每个坦克在决策处理时可能用到的一些高级属性，按需取用！
	struct tagTankStatusAdv
	{
		//注意，以下三行变量是初步数据，即没有敌方坦克干扰时的情况
		int numDscDir = 0;//min_step下降的方向数，包含了=0和=1的情况
		//dsc表示descending
		//若有这样的方向，以下变量有意义：
		Action dscDir=Stay;//下降的方向（若有多个方向，随机取其中的一个）
		int tx=0, ty=0;//移动或射击的目的地

		//这回合能否射击
		bool fireable = true;

		//考虑双方坦克干扰
		bool blocked = false;//是否被敌方坦克限制住了
		int consecutive_blocked_terms = 0;//截至上一回合决策结束时，这一坦克被敌方坦克连续卡住的回合数
		//只在blocked=true时有效；只在我方坦克上有意义；其维护利用了data字段

		bool force_to_defend = false;//强制防御——一旦开启就坚决不进攻，除非对位敌方坦克被干掉了
		//只对友方坦克有意义，由data字段维护
		//4回合后，一旦防御一次就会设为true
	};
	tagTankStatusAdv tankStatusAdv[sideCount][tankPerSide];


	
	bool has_tank(int, int);
	//辅助函数：在(x,y)处是否有敌方（相对side方）坦克
	bool has_enemy_tank(int side, int x, int y)
	{
		if (side == Red)
			return (field->gameField[y][x] & Blue0) || (field->gameField[y][x] & Blue1);
		//if (side == Blue)
		else
			return (field->gameField[y][x] & Red0) || (field->gameField[y][x] & Red1);
	}
	bool enemy_may_arrive(int mySide,int x, int y)
	{
		if (has_enemy_tank(mySide, x, y)) return true;
		for (int dir = 0; dir < 4; dir++)
		{
			int tx = x + dx[dir];
			int ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			if (has_enemy_tank(mySide, tx, ty))
				return true;
		}
		return false;
	}

	//产生一个坦克在(x,y)处能射到的范围，结果写入arr数组，1表示能，0表示不能射到
	//注意函数重载！！
	void generate_shoot_range(int x, int y, int(*arr)[9])
	{
		//初始化
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++)
				arr[i][j] = 0;
		for (int t = 1;; t++)//向右找
		{
			if (!CoordValid(x + t, y)) break;
			if (field->gameField[y][x + t] == None || field->gameField[y][x + t] == Water)
				arr[y][x + t] = 1;
			else
			{
				if (has_tank(x + t, y)) arr[y][x + t] = 1;
				break;
			}
		}
		for (int t = 1;; t++)//向左找
		{
			if (!CoordValid(x - t, y)) break;
			if (field->gameField[y][x - t] == None || field->gameField[y][x - t] == Water)
				arr[y][x - t] = 1;
			else
			{
				if (has_tank(x - t, y)) arr[y][x - t] = 1;
				break;
			}
		}
		for (int t = 1;; t++)//向下找
		{
			if (!CoordValid(x, y + t)) break;
			if (field->gameField[y + t][x] == None || field->gameField[y + t][x] == Water)
				arr[y + t][x] = 1;
			else
			{
				if (has_tank(x, y + t)) arr[y + t][x] = 1;
				break;
			}
		}
		for (int t = 1;; t++)//向上找
		{
			if (!CoordValid(x, y - t)) break;
			if (field->gameField[y - t][x] == None || field->gameField[y - t][x] == Water)
				arr[y - t][x] = 1;
			else
			{
				if (has_tank(x, y - t)) arr[y - t][x] = 1;
				break;
			}
		}
	}
	//产生在(x,y)处，在哪个范围里能射到(x,y)处，结果写入arr数组，1表示能，0表示不能被射到
	//shot代表 被 射到
	void generate_shot_range(int x, int y, int(*arr)[9])
	{
		//初始化
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++)
				arr[i][j] = 0;
		for (int t = 1;; t++)//向右找
		{
			if (!CoordValid(x + t, y)) break;
			if (field->gameField[y][x + t] == None)
				arr[y][x + t] = 1;
			else if (field->gameField[y][x + t] == Water);//是水域的话循环继续，但不在arr中标记
			else 
			{
				
				break;
			}
		}
		for (int t = 1;; t++)//向左找
		{
			if (!CoordValid(x - t, y)) break;
			if (field->gameField[y][x - t] == None)
				arr[y][x - t] = 1;
			else if (field->gameField[y][x - t] == Water);
			else 
			{
				
				break;
			}
				
		}
		for (int t = 1;; t++)//向下找
		{
			if (!CoordValid(x, y + t)) break;
			if (field->gameField[y + t][x] == None)
				arr[y + t][x] = 1;
			else if (field->gameField[y + t][x] == Water);
			else 
			{
				break;
			}
		}
		for (int t = 1;; t++)//向上找
		{
			if (!CoordValid(x, y - t)) break;
			if (field->gameField[y - t][x] == None)
				arr[y - t][x] = 1;
			else if (field->gameField[y - t][x] == Water);
			else 
			{
				
				break;
			}
		}
	}


	bool has_tank(int x, int y)
	{
		return (field->gameField[y][x] & Blue0) || (field->gameField[y][x] & Blue1)
			|| (field->gameField[y][x] & Red0) || (field->gameField[y][x] & Red1);
	}
	void generate_adv_tank_status()
	{
		//本回合是否能射击
		for (int side = 0; side < sideCount; side++)
		{
			for (int tank = 0; tank < tankPerSide; tank++)
			{
				tankStatusAdv[side][tank].fireable =
					!(field->previousActions[field->currentTurn - 1][side][tank] > Left);
			}

		}
		//先生成梯度下降方向相关数据
		for (int side = 0; side < sideCount; side++)
		{
			for (int tank = 0; tank < tankPerSide; tank++)
			{
				for (int dir = 0; dir < 4; dir++)
				{
					int x = field->tankX[side][tank];
					int y = field->tankY[side][tank];
					int x1 = x + dx[dir];
					int y1 = y + dy[dir];
					if (!CoordValid(x1, y1)) continue;
					if (min_step_to_base[side][y1][x1] == -1) continue;
					if (min_step_to_base[side][y1][x1] < min_step_to_base[side][y][x])
					{
						tankStatusAdv[side][tank].numDscDir++;
						tankStatusAdv[side][tank].dscDir = (Action)dir;
						tankStatusAdv[side][tank].tx = x1;
						tankStatusAdv[side][tank].ty = y1;
					}
				}
				//特判
				int x = field->tankX[side][tank];
				int y = field->tankY[side][tank];
				if (has_unique_dsc_dir(side, x, y))
				{
					int dir = get_unique_dsc_dir(side, x, y);
					tankStatusAdv[side][tank].tx = x + dx[dir];
					tankStatusAdv[side][tank].ty = y + dy[dir];
				}
			}
		}
		
		//判断是否被敌方坦克卡住
		for (int side = 0; side < sideCount; side++)
		{
			for (int tank = 0; tank < tankPerSide; tank++)
			{
				tagTankStatusAdv& t = tankStatusAdv[side][tank];
				bool& blocked = tankStatusAdv[side][tank].blocked;

				//卡住有两种情况
				//第一种情况：我要走过去的空地在敌方坦克射程内
				blocked = true;
				//这有三个条件，1 我要走过去
				blocked = blocked && (tankStatusAdv[side][tank].numDscDir == 1);
				if (blocked) blocked = blocked && (field->gameField[t.ty][t.tx] == None);
				//2 我现在的位置不再敌方射程之内（不然就不是被卡住，而是皇城PK了
				int& x = field->tankX[side][tank];
				int& y = field->tankY[side][tank];
				if (blocked) blocked = blocked && (real_shot_range[side ^ 1][y][x] == 0.0f);
				//3 目标位置在敌方射程之内
				if (blocked) blocked = blocked && (real_shot_range[side ^ 1][t.ty][t.tx] > 0);
				if (blocked) continue;

				//第二种情况：我和敌方坦克只有一墙之隔，谁先射谁倒霉
				blocked = true;
				//这有两个条件，1 我有一堵要射的墙在我的最短路上
				blocked = blocked && (tankStatusAdv[side][tank].numDscDir == 1);
				if (blocked) blocked = blocked && (field->gameField[t.ty][t.tx] == Brick);
				//2 墙的后面有一个敌方坦克——大约等价于，这堵墙在地方射程范围内
				int ex = t.tx + dx[t.dscDir];
				int ey = t.ty + dy[t.dscDir];//可能的敌人的位置
				bool dangerousEnemyBehindWall = false;
				//找对面的敌方坦克
			
				for (; CoordValid(ex, ey) && (field->gameField[ey][ex] == None || field->gameField[ey][ex] == Water || has_enemy_tank(side, ex, ey));
					ex += dx[t.dscDir], ey += dy[t.dscDir])
				{
					if (enemy_may_arrive(side, ex, ey))//对面的敌方坦克找到了！
					{
						dangerousEnemyBehindWall = true;
						goto _tmp_finished;
					}
				}
			_tmp_finished:
				blocked = blocked && dangerousEnemyBehindWall;
			}
		}

		//更新consecuteve_blocked_terms字段
		int mySide = field->mySide;
		for (int tank = 0; tank < tankPerSide; tank++)
		{
			if (tankStatusAdv[mySide][tank].blocked)
				tankStatusAdv[mySide][tank].consecutive_blocked_terms++;
			else
				tankStatusAdv[mySide][tank].consecutive_blocked_terms = 0;
		}
	}

	int std2sca(int act)
	{
		if (act < 0) return act;
		else if (act < 4)
		{
			if (act == Down)
				act = 0;
			else if (act == Up)
				act = 1;
			else if (act == Left)
				act = 3;
			else if (act == Right)
				act = 2;
			return act;
		}
		else
		{
			act -= 4;
			if (act == Down)
				act = 0;
			else if (act == Up)
				act = 1;
			else if (act == Left)
				act = 3;
			else if (act == Right)
				act = 2;
			return act + 4;
		}
	}
	void _add_arr(int(*added)[9], int(*add)[9])
	{
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++)
				added[i][j] = added[i][j] + add[i][j];
	}
	inline int mht_dis(int x1, int y1, int x2, int y2)
	{
		return abs(x1 - x2) + abs(y1 - y2);//曼哈顿距离
	}
	void print_arr(int(*arr)[9])
	{
		for (int i = 0; i < 9; i++)
		{
			for (int j = 0; j < 9; j++)
			{
				cout << arr[i][j] << " ";
			}
			cout << endl;
		}
		system("pause");
	}
	void get_revising_defense_act(int tank, int enemyTank)
	{
		int mySide = field->mySide;
		int enemySide = mySide ^ 1;

		//我方防御坦克的位置
		int x = field->tankX[mySide][tank];
		int y = field->tankY[mySide][tank];
		//敌方被防御坦克的位置 e-enemy
		int ex = field->tankX[enemySide][enemyTank];
		int ey = field->tankY[enemySide][enemyTank];
		//敌方被防御坦克预计下一步要走到的位置 t-target
		int etx = tankStatusAdv[enemySide][enemyTank].tx;
		int ety = tankStatusAdv[enemySide][enemyTank].ty;

		//防御有着几条条件。若不满足，则不修改通用AI已经做出的条件：
		//1 敌方坦克不具唯一梯度下降方向，防御时机不好
		//if (tankStatusAdv[enemySide][enemyTank].numDscDir != 1)
		//	return;
		
		//sca要求的特判
		extern bool stay_for_beat[2];
		if (stay_for_beat[tank])
		{
			if (my_action[tank] == Stay)
				return;
		}
		//3 我方坦克被卡住了——这基本意味着向前走就是挨敌方坦克的打
		if (tankStatusAdv[mySide][tank].blocked)
			return;
		
		

		

		//核心
		//0 最稳妥的方法：永远卡在敌方坦克的必经之路上，对面就算是天神下凡也别想过去
		//if (has_unique_dsc_dir(enemySide, etx, ety))//得提前一步预判
		if(has_unique_dsc_dir(enemySide, ex, ey) && has_unique_dsc_dir(enemySide,etx,ety))
		{
			int dir1 = get_unique_dsc_dir(enemySide, etx, ety);
			int ettx = etx + dx[dir1];
			int etty = ety + dy[dir1];//敌人两步后的位置

			//如果已经卡住——那都已经固若金汤了，那就不搞别的防御策略了
			if (x == etx && y == ety)
				return;
			if (x == ettx && y == etty)
				return;
			if (is_none(etx, ety) && is_none(ettx, etty))
			{
				for (int dir = 0; dir < 4; dir++)
				{
					//四周四个方向
					int tx = x + dx[dir];
					int ty = y + dy[dir];
					if (!CoordValid(tx, ty)) continue;
					//若往那个方向走能~，则改变策略，进行防御
					if (tx==ettx && ty==etty && real_shot_range[enemySide][ty][tx] == 0.0f)
					{
						if (field->gameField[ty][tx] == Brick && real_shot_range[enemySide][y][x] == 0.0f)
							my_action[tank] = (Action)std2sca(dir + 4);
						else if (field->gameField[ty][tx] == None)
							my_action[tank] = (Action)std2sca(dir);
						return;
					}
				}
			}
		}


		//如果不能一步卡到，就提前卡住敌方坦克的最短路，挡差
		//基地周围一圈必经之路加一点权重
		if (field->currentTurn > 7)
		{
			if (mySide == Blue)
			{
				//min_path[enemySide][enemyTank][0][3] += 1;
				//min_path[enemySide][enemyTank][0][5] += 1;
				//min_path[enemySide][enemyTank][1][4] += 1;
				if (min_step_to_base[enemySide][ey][ex] <= 3 && ey == 0 && ex <= 2)
					min_path[enemySide][enemyTank][1][4] += 3;
				else if (min_step_to_base[enemySide][ey][ex] <= 3 && ey <= 1 && ex >= 6)
					min_path[enemySide][enemyTank][0][5] += 3;
				else if (min_step_to_base[enemySide][ey][ex] <= 3 && ey <= 1 && ex <= 2)
					min_path[enemySide][enemyTank][0][3] += 3;
				else if (ey == 0 && ex >= 6)
					min_path[enemySide][enemyTank][0][5] += 3;
				else if (ey == 0 && ex <= 2)
					min_path[enemySide][enemyTank][0][3] += 3;
				else if (ex == 4)
					min_path[enemySide][enemyTank][1][4] += 3;
				else if (ex >= 5)
					min_path[enemySide][enemyTank][1][5] += 5;
				else if (ex <= 3)
					min_path[enemySide][enemyTank][1][5] += 5;
			}
			else
			{
				if (min_step_to_base[enemySide][ey][ex] <= 3 && ey == 0 && ex <= 2)
					min_path[enemySide][enemyTank][7][4] += 3;
				else if (min_step_to_base[enemySide][ey][ex] <= 3 && ey >= 7 && ex >= 6)
					min_path[enemySide][enemyTank][8][5] += 3;
				else if (min_step_to_base[enemySide][ey][ex] <= 3 && ey >= 7 && ex <= 2)
					min_path[enemySide][enemyTank][8][3] += 3;
				else if (ey == 8 && ex >= 6)
					min_path[enemySide][enemyTank][8][5] += 3;
				else if (ey == 8 && ex <= 2)
					min_path[enemySide][enemyTank][8][3] += 3;
				else if (ex == 4)
					min_path[enemySide][enemyTank][7][4] += 3;
				else if (ex >= 5)
					min_path[enemySide][enemyTank][7][5] += 5;
				else if (ex <= 3)
					min_path[enemySide][enemyTank][7][3] += 5;
			}
		}
		int best_dir = -1;
		int best_my_value = 0x7fffff;
		int best_enemy_value = min_path[enemySide][enemyTank][y][x];//原始：和原地呆着不动相比
		
		for (int dir = 0; dir < 4; dir++)
		{
			//四周四个方向
			int tx = x + dx[dir];
			int ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			//若往那个方向走最有可能（在未来的某一回合）能挡住敌方坦克，则改变策略，进行防御
			if (min_path[enemySide][enemyTank][ty][tx])
			{
				//同时，如果也能减小我离敌方基地距离，那更好
				//后来注：经实战发现还是不要这一条比较好...
				/*if (min_step_to_base[mySide][ty][tx] < best_my_value)
				{
				best_dir = dir;
				best_my_value = min_step_to_base[mySide][ty][tx];
				best_enemy_value = min_path[enemySide][enemyTank][ty][tx];
				}
				else if (min_step_to_base[mySide][ty][tx] = best_my_value)
				{*///往更有可能把对面挡住的方向走
				if (min_path[enemySide][enemyTank][ty][tx] > best_enemy_value)
				{
					best_dir = dir;
					//best_my_value = min_step_to_base[mySide][ty][tx];
					best_enemy_value = min_path[enemySide][enemyTank][ty][tx];
				}
			}
		}
		if (best_dir == -1 && best_enemy_value != 0)//若原地已经能很好的挡住，那就不动
		{
			if (my_action[tank] >= 0 && my_action[tank] <= 3 && real_shot_range[enemySide][y][x]==0.0f)
				my_action[tank] = Stay;
			return;
		}
		if (best_dir != -1)
		{
			int tx = x + dx[best_dir];
			int ty = y + dy[best_dir];
			if (real_shot_range[enemySide][ty][tx] > 0.0f)
				return;
			//特判：若双方坦克已经很接近，我向前会导致和敌方坦克重合，那挡拆就毫无效果了，那就不挡拆
			if (field->gameField[ty][tx] == None && (ty == ety && tx == etx))
				return;
			if (field->gameField[ty][tx] == Brick && real_shot_range[enemySide][y][x] == 0.0f)//注意，这里可能需要射击
			{
				my_action[tank] = (Action)std2sca(best_dir+4);
			}
			else
				my_action[tank] = (Action)std2sca(best_dir);
			return;
		}

		//额外特判：如果现在有生命危险...那还是交给能保命的通用AI吧（这来自于某个bug）
		if (real_shot_range[enemySide][y][x] > 0.0f)
			return;
		//经验证明，这一手最好在还没开打的时候弄...不然打起来了再玩这个实在是过于愚蠢
		//参考：https://www.botzone.org.cn/match/5ce988e3d2337e01c7aca364
		//判断交火互卡：我方坦克与敌方坦克互相在射程中，且互相在对方的最短路上
		if (shot_range[enemySide][y][x] >= 0.0f && shot_range[mySide][ey][ex] >= 0.0f &&
			min_path[enemySide][enemyTank][y][x] && min_path[mySide][tank][ey][ex])
			return;
		//2 如果现在的位置已经卡住对面了，那就不管了
		if (tankStatusAdv[enemySide][enemyTank].blocked)
		{
			//有60%的几率改为stay，继续卡住对面
			if ((rand() % 100) > 40 && (my_action[tank] >= 4 || !tankStatusAdv[mySide][tank].fireable))
				my_action[tank] = Stay;
			return;
		}

		//这个数组表示有哪些位置能卡住enemyTank，用01表示
		int blocking_range[9][9];
		memset(blocking_range, 0, sizeof(blocking_range));
		//注意，现在走的一步是为了下一步卡住敌方坦克，所以计算的是地方坦克路径上的位置的blocking-range.
		//能卡住敌方坦克，有这几种种情况：

		//如果能在一步之遥之内卡住敌方坦克，那最好
		//1 能把对面坦克简单地卡住（一步之内）
		if(etx!=4)//中线特判：如果对面已经到我方中线上了...那就不卡移动位置了，因为卡不住，对面直接推家就好了
			generate_shot_range(etx,ety, blocking_range);
	
		//2 两个坦克一墙之隔，谁先射墙谁马上倒霉
		if (field->gameField[ety][etx] == Brick)
		{
			int tx = 2 * etx - ex;//墙对面的位置
			int ty = 2 * ety - ey;
			if (CoordValid(tx, ty))
				if (field->gameField[ty][tx] == None)
					blocking_range[ty][tx] = 1;
		}
		for (int dir = 0; dir < 4; dir++)
		{
			//四周四个方向
			int tx = x + dx[dir];
			int ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			//若往那个方向走最能卡住敌方坦克，则改变策略，进行防御
			if (blocking_range[ty][tx])
			{
				my_action[tank] = (Action)std2sca(dir);
			}
		}


		////一步之内卡不到，则考虑后面几步
		//memset(blocking_range, 0, sizeof(blocking_range));
		////1 能射到路径上某一点的位置 
		//for (int i = 0; i < 9; i++)
		//{
		//	for (int j = 0; j < 9; j++)
		//	{
		//		if (j == 4) continue;//同理，中线特判
		//		if (min_path[enemySide][enemyTank][i][j])//对 敌方坦克路径上的每一点，找能将其卡住的位置
		//		{
		//			int tmp[9][9];
		//			generate_shot_range(j, i, tmp);
		//			for (int ii = 0; ii < 9; ii++)
		//			{
		//				for (int jj = 0; jj < 9; jj++)
		//				{
		//					tmp[ii][jj] *= min_path[enemySide][enemyTank][i][j];//加上一些权重
		//				}
		//			}
		//			_add_arr(blocking_range, tmp);
		//		}
		//	}
		//}
		//best_dir = -1;
		//int best_blocking_range = 0;
		////得到了blocking_range，然后做进一步决策
		//for (int dir = 0; dir < 4; dir++)
		//{
		//		//四周四个方向
		//	int tx = x + dx[dir];
		//	int ty = y + dy[dir];
		//	if (!CoordValid(tx, ty)) continue;
		//	//若往那个方向走最有可能（在未来的某一回合）能卡住敌方坦克，则改变策略，进行防御
		//	if (blocking_range[ty][tx] > best_blocking_range)
		//	{
		//		best_dir = dir;
		//		best_blocking_range = blocking_range[ty][tx];
		//	}
		//}
		//if (best_dir != -1)
		//{
		//	my_action[tank] = (Action)std2sca(best_dir);
		//	return;
		//}

		
		//什么？这都没放到对面坦克？究极压箱底策略：往步数大的地方反向走——这样会回退到起点附近，然后就容易卡到敌方坦克了
		int r_step[9][9];

		//一波小小的bfs
		{
			for (int i = 0; i < 9; i++)
				for (int j = 0; j < 9; j++)
					r_step[i][j] = -1;

			queue<pair<int, int>> q;
			pair<int, int> begin;
			if (mySide == Blue)
				if (tank == 0)
					begin = make_pair(3, 1);
				else
					begin = make_pair(5, 1);
			else
				if (tank == 0)
					begin = make_pair(5, 7);
				else
					begin = make_pair(3, 7);
			r_step[begin.second][begin.first] = 0;
			q.push(begin);
			while (!q.empty())
			{
				int x = q.front().first;
				int y = q.front().second;
				q.pop();
				for (int dir = 0; dir < 4; dir++)
				{
					int tx = x + dx[dir];
					int ty = y + dy[dir];
					if (!CoordValid(tx, ty)) continue;
					if (field->gameField[ty][tx] ==Steel || field->gameField[ty][tx] == Water
						|| field->gameField[ty][tx] == Base) continue;
					if (r_step[ty][tx] == -1 || 
						(field->gameField[ty][tx] == Brick && r_step[ty][tx] > r_step[y][x] + 2) ||
						(field->gameField[ty][tx] != Brick && r_step[ty][tx] > r_step[y][x] + 1))
					{
						if(field->gameField[ty][tx] !=Brick)
							r_step[ty][tx] = r_step[y][x] + 1;
						else
							r_step[ty][tx] = r_step[y][x] + 2;
						q.push(make_pair(tx, ty));
					}

				}
			}
		}
		//得到了r_step数组
		//找出最优方向
		best_dir = -1;
		int min_step = 10;
		for (int dir = 0; dir < 4; dir++)
		{
			int tx = x + dx[dir];
			int ty = y + dy[dir];
			if (!CoordValid(tx, ty)) continue;
			if (r_step[ty][tx] == -1) continue;
			if (r_step[ty][tx] <min_step)
			{
				best_dir = dir;
				min_step = r_step[ty][tx];
			}
		}
		if (best_dir != -1)
		{
			int tx = x + dx[best_dir];
			int ty = y + dy[best_dir];
			if (field->gameField[ty][tx] == Brick)//注意，这里可能需要射击
				best_dir += 4;
			my_action[tank] = (Action)std2sca(best_dir);
			return;
		}
	}

	void decode_data(string data)
	{
		if (field->currentTurn == 1) return;
		stringstream ss{ data };
		for (int tank = 0; tank < tankPerSide; tank++)
			ss >> tankStatusAdv[field->mySide][tank].consecutive_blocked_terms;
		for (int tank = 0; tank < tankPerSide; tank++)
			ss >> tankStatusAdv[field->mySide][0].force_to_defend;
		if (!ss)
			throw runtime_error{ "error decoding data!" };
	}
	void encode_data(string& data)
	{
		stringstream ss;
		ss << tankStatusAdv[field->mySide][0].consecutive_blocked_terms << " ";
		ss << tankStatusAdv[field->mySide][1].consecutive_blocked_terms << " ";
		ss << tankStatusAdv[field->mySide][0].force_to_defend << " ";
		ss << tankStatusAdv[field->mySide][1].force_to_defend << " ";
		data = ss.str();
	}
	//决策前的预处理
	void pre_process()
	{
		genarate_min_step(0);
		genarate_min_step(1);
		generate_min_path();
		generate_shot_range(0);
		generate_shot_range(1);
		generate_shot_range(0, false);
		generate_shot_range(1, false);

		generate_adv_tank_status();

		Debug_Print_MinStep();
	}

	int cnt = 0;
	bool avoid_failed = false, stay_for_beat[2] = { false,false };
	//基于最短路的傻瓜策略
	inline bool CanSafelyShoot(int dir, int wi, int wj, int tx, int ty, int side) {
		//目前只能判断左右
		int ii = wi+next_step[dir][0], jj = wj+next_step[dir][1];
		int uc, dc;
		for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]);
		uc = next_step[dir][0] ? ii : jj;
		ii = tx; jj = ty;
		for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir ^ 1][0], jj += next_step[dir ^ 1][1]);
		dc = next_step[dir ^ 1][0] ? ii : jj;
		if (uc > dc) std::swap(uc, dc);
		//uc dc: 该方向上，可以射到tank的坐标范围
		for (uc++, dc--; uc <= dc; uc++) {
			if ((dir < 2 && !ItemIsAccessible(field->gameField[uc][ty])) || (dir >= 2 && !ItemIsAccessible(field->gameField[tx][uc]))) continue;
			for (int bias = -1; bias <= 1; bias++) {
				if (dir >= 2) {//左右
					if (ty == uc && bias)continue;
					//if (uc == wj) continue;
					if (uc > min(ty, wj) && uc < max(ty, wj)) continue;
					if (CoordValid(tx + bias, uc) && ((IsTank(field->gameField[tx + bias][uc]) && GetTankSide(field->gameField[tx + bias][uc]) != side)
						|| HasMultipleTank(field->gameField[tx + bias][uc])))
						return false;
				}
			}
		}
		return true;
	}
	inline bool CanGetThrough(int tx, int ty, int side) {
		int tank_count = 0, total_count = 0;
		for (int dir = 0; dir < 4; dir++) {
			tank_count = 0;
			for (int ii = tx, jj = ty; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]) {
				if ((IsTank(field->gameField[ii][jj]) && GetTankSide(field->gameField[ii][jj]) != side)
					|| HasMultipleTank(field->gameField[ii][jj])) {
					total_count++;
					tank_count++;
				} //敌军，上！
			}
			if (tank_count == 2) return true; //同一方向有两个坦克，安全
		}
		if (total_count == 2) return false; //在两个坦克射程内且不在同一方向，危险
		return true; //其余情况，安全
	}

	int get_stupid_action(int tank_id) {
		bool force_move_mode = false;
		int side = field->mySide;
		if (++cnt > 5) return -2;
		my_action[tank_id] = -2;
		if (!field->tankAlive[side][tank_id]) return my_action[tank_id] = -1; //坦克已死，没你的事了

		int tx = field->tankY[side][tank_id], ty = field->tankX[side][tank_id]; //当前tank坐标
		int fx = field->tankY[side][tank_id ^1], fy = field->tankX[side][tank_id^1]; //另一个友方tank坐标
		if (my_action[tank_id ^ 1] >= 0 && my_action[tank_id ^ 1] <= 3) {
			fx += next_step[my_action[tank_id ^ 1]][0];
			fy += next_step[my_action[tank_id ^ 1]][1];
		}

		if (field->previousActions[field->currentTurn - 1][side][tank_id] > Left) force_move_mode = true; //上一步是射子弹

		//↓一下可射到基地的特判
		bool go_out_if = false;
		if ((min_step_to_base[side][tx][ty] == 1 || tx == baseY[side^1]) && !avoid_failed) {
			if (!force_move_mode && (min_step_to_base[side][tx][ty] == 1 || real_shot_range[side^1][tx][ty]<=0.001)) {
				if (baseX[side ^ 1] == ty) { my_action[tank_id] = side + 4;} //同一竖行，则向前射
				else { my_action[tank_id] = 4 + (baseX[side ^ 1] < ty ? 3 : 2); } //同一横行，则向基地射
				if (min_step_to_base[side][field->tankY[side][tank_id ^ 1]][field->tankX[side][tank_id ^ 1]] == 1
					&& field->previousActions[field->currentTurn - 1][side][tank_id ^ 1] <= Left
					&& ty==4 && field->tankX[side][tank_id ^ 1]==4 && abs(tx-baseY[side^1])>abs(field->tankY[side][tank_id ^ 1] -baseY[side^1])) {
					my_action[tank_id] = -1;
				}
			}
			else {
				int ansss = Stay;//默认不动
				int gx, gy;
				bool avoid_friend = min_step_to_base[side][fx][fy] == 1 && shoot_friend(side, tank_id ^ 1, tx, ty);
				double risk = shot_range[side ^ 1][tx][ty], rfactor = GetRandom() + 0.5; //选取为1且射中风险最小的位置
				if (avoid_friend) risk = 1000;
				for (int dir = 0; dir < 4; dir++) {
					gx = tx + next_step[dir][0];
					gy = ty + next_step[dir][1];
					if (!CoordValid(gx, gy)) continue;
					if (avoid_friend &&  shoot_friend(side, tank_id ^ 1, gx, gy)) continue;
					if (ItemIsAccessible(field->gameField[gx][gy], true)) {
						double temp = shot_range[side ^ 1][gx][gy];
						if (!avoid_friend) temp += (min_step_to_base[side][gx][gy] - 0.9)*rfactor; //1的风险系数比2小很多
						if (risk > shot_range[side ^ 1][gx][gy]) {
							risk = shot_range[side ^ 1][gx][gy];
							ansss = dir;
						}
						/*else if (abs(risk-temp)<1e-7 && GetRandom() < 0.6) {
							
						}*/
					}
				}
				my_action[tank_id] = ansss;
				if (risk > 0.001 && real_shot_range[side^1][tx][ty]>=0.001 && !force_move_mode) {
					go_out_if = true;
				}
				if (!go_out_if && ansss == Stay && avoid_friend) {
					avoid_failed = true;
					get_stupid_action(tank_id ^ 1);
				}
			}
			if (!go_out_if) {
				if (shoot_friend(side, tank_id, fx, fy) && !avoid_failed)
					get_stupid_action(tank_id ^ 1);
				return my_action[tank_id];
			}
		}
		
		int Ignore_tankid = -1;
		if (HasMultipleTank(field->gameField[tx][ty])) {
			int shot_side = IsUniqueDir(side ^ 1, tx, ty);
			if (shot_side >= 0 && min_step_to_base[side ^ 1][tx][ty] <= min_step_to_base[side][tx][ty] + 2) {
				int tid = -1;
				for (int i = 0; i < tankPerSide; i++) {
					if (field->tankY[side ^ 1][i] == tx && field->tankX[side ^ 1][i] == ty) {
						tid = i; break;
					}
				}
				if (tid >= 0) {
					Coordinate etc{ tx,ty }, tc{ tx,ty };
					etc.Rev(field->previousActions[field->currentTurn - 1][side ^ 1][tid]);
					tc.Rev(field->previousActions[field->currentTurn - 1][side][tank_id]);
					if (etc != tc) {
						Coordinate cord = shoot_coord(shot_side, tx, ty);
						my_action[tank_id] = shot_side + 4;
						if (!shoot_friend(side, tank_id, fx, fy) && (!CoordValid(cord.x,cord.y) || min_path[side^1][tid^1][cord.x][cord.y]==0)
							&& cord.x!=baseY[side] && GetRandom() <= 0.2)
							return my_action[tank_id];
						my_action[tank_id] = -2;
					}
					/*if (GetRandom() < 0.4) {
						etc.Rev(field->previousActions[field->currentTurn - 2][side ^ 1][tid]);
						tc.Rev(field->previousActions[field->currentTurn - 2][side][tank_id]);
					}*/
					if (etc.x==tc.x && etc.y==tc.y) {
						Ignore_tankid = tid;
						my_action[tank_id] = -2;
					}
				}
			}
		}

		//0下 1上 2右 3左  权重
		double act[4] = { -1,-1,-1,-1};
		for (int i = 0; i < 4; i++) {
			int gx = tx + next_step[i][0], gy = ty + next_step[i][1];
			if (!CoordValid(gx, gy)) continue;
			if (shoot_friend(side, tank_id ^ 1, gx, gy)) continue;
			if (!CanGetThrough(gx, gy, side)) continue; //注意：需要测试
			if (min_step_to_base[side][tx][ty] >= min_step_to_base[side][gx][gy] - 1 && min_step_to_base[side][gx][gy]>=0) {
				act[i] = min_step_to_base[side][tx][ty] - min_step_to_base[side][gx][gy] + 0.3;
				if ((ty - 4)*(fy - 4) < 0 && gy == 4 && IsUniqueDir(side, gx, gy) == i) act[i] -= 0.5;
				if (field->gameField[gx][gy] == Brick && force_move_mode) act[i] = -1.8;
			}
			act[i] += 0.8;
			if (my_action[tank_id ^ 1] != -2 && gx==fx && gy==fy) {
				act[i] = -0.1;
			}
		}
		//↑先把合法的弄成非负

		//若在敌方伪射程之内
		if (shot_range[side ^ 1][tx][ty] > 0) {
			int ans = Stay, tid = -1, etx = 0, ety = 0;
			// 不要怂 直接刚 看看是哪个方向
			for (int dir = 0; dir < 4; dir++) {
				for (int ii = tx, jj = ty; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]) {
					if (fx == ii && fy == jj)break; //停火，友军！
					if (IsTank(field->gameField[ii][jj]) && GetTankSide(field->gameField[ii][jj]) != side) {
						tid = GetTankID(field->gameField[ii][jj]);
						ans = dir; etx = ii; ety = jj;
						break;
					} //敌军，上！
				}
				if (ans >= 0 && !(field->previousActions[field->currentTurn - 1][side ^ 1][tid] > Left)) break;
				//若这个tank上回合发射了子弹，先存着，看看有没有其他
			}
			if (ans >= 0 && !force_move_mode) {
				if (min_step_to_base[side][tx][ty] <= min_step_to_base[side ^ 1][etx][ety]) {
					if (!(field->previousActions[field->currentTurn - 1][side ^ 1][tid] > Left)) {
						//我方更近，尽可能不参与对峙（若这个tank上回合发过子弹则忽略tank对峙，不进入此if）
						double mrisk = 10;
						int ans2 = Stay, mdis = 100;
						for (int dir = 0; dir < 4; dir++) {
							if (!CoordValid(tx + next_step[dir][0], ty + next_step[dir][1]) || !ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false)) continue;
							if (mrisk > shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
								ans2 = dir; mrisk = shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]];
								mdis = min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]];
							}
							else if (mrisk == shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
								if (mdis > min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
									ans2 = dir; mdis = min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]];
								}
							}
						}
						if (mrisk > 0 || min_step_to_base[side][tx][ty] <= mdis || min_step_to_base[side][tx][ty] > min_step_to_base[side][fx][fy])
						{
							my_action[tank_id] = ans + 4; return my_action[tank_id];
						} //保命第一位，干
						else { my_action[tank_id] = ans2; return my_action[tank_id]; } //朝0风险中 最低的走
					}
					else if (min_step_to_base[side][tx][ty] >= min_step_to_base[side][etx][ety]) { //对方tank离对方基地更近
						my_action[tank_id] = ans + 4; return my_action[tank_id]; //干他
					}
				}
				else {
					//对方更近，直接上
					/*
					int shoot_range1 = IsUniqueDir(side, tx, ty), shoot_range2 = IsUniqueDir(side ^ 1, etx, ety);
					if ((shoot_range1 > 0 && InShootRange(etx, ety, tx + next_step[shoot_range1][0], ty + next_step[shoot_range1][1]))
						|| (shoot_range2 >0 && InShootRange(tx,ty,etx+next_step[shoot_range2][0],ety+next_step[shoot_range2][1])) )*/
					{my_action[tank_id] = ans + 4; return my_action[tank_id]; }
				}
			}
			else if (ans >= 0 && force_move_mode && !(field->previousActions[field->currentTurn - 1][side ^ 1][tid] > Left)) {
				double mrisk = 10;
				int ans2 = Stay, mdis = 100;
				for (int dir = 0; dir < 4; dir++) {
					if (!ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false)) continue;
					if (mrisk > shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
						ans2 = dir; mrisk = shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]];
						mdis = min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]];
					}
					else if (mrisk == shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
						if (mdis > min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]]) {
							ans2 = dir; mdis = min_step_to_base[side][tx + next_step[dir][0]][ty + next_step[dir][1]];
						}
					}
				}
				my_action[tank_id] = ans2; return my_action[tank_id];
			}
			else if (real_shot_range[side ^ 1][tx][ty] < 0.001 && min_step_to_base[side][tx][ty] >= min_step_to_base[side ^ 1][etx][ety] && (etx - 4)*(side - 0.5) >= 0
				&& (etx - tx)*(side - 0.5) <= 0) {
				stay_for_beat[tank_id] = true;
			}
			else if (real_shot_range[side ^ 1][tx][ty] < 0.001 && min_step_to_base[side][tx][ty] < min_step_to_base[side ^ 1][tx][ty]
				&& min_step_to_base[side][tx][ty] > min_step_to_base[side][etx][ety]
				&& min_step_to_base[side^1][etx][ety] > min_step_to_base[side^1][tx][ty]
				&& abs(etx - tx) + abs(ety - ty) == 1 && GetRandom() < 0.7) {
				//后退一步 新增 注：尚未调试
				int ans2 = -1;
				for (int dir = 0; dir < 4; dir++) {
					if (!ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false)) continue;
					if (!InShootRange(field->tankY[side^1][tid^1],field->tankX[side^1][tid^1], tx + next_step[dir][0], ty + next_step[dir][1])
						&& !(fx== tx + next_step[dir][0] && fy== ty + next_step[dir][1])) {
						ans2 = dir;  break;
					}
				}

				if (ans2 != -1) {
					my_action[tank_id] = ans2;
					if (!shoot_friend(side, tank_id, fx, fy))
						return my_action[tank_id] = ans2;
					else
						my_action[tank_id] = -2;
				}
			}
			
		}

		int shot_dir;
		if(!force_move_mode) //预判走位+开炮
			for (int i = 0; i < tankPerSide; i++) {
				if (tx == field->tankY[side ^ 1][i] && ty == field->tankX[side ^ 1][i]) continue;
				shot_dir = IsUniqueDir(side ^ 1, field->tankY[side ^ 1][i], field->tankX[side ^ 1][i]);
				if (shot_dir >= 0 && InShootRange(tx, ty, field->tankY[side ^ 1][i] + next_step[shot_dir][0], field->tankX[side ^ 1][i] + next_step[shot_dir][1], false, side^1)) {
					if (field->previousActions[field->currentTurn - 1][side ^ 1][i] > Left || GetRandom() <= 0.95) {
						int etx = field->tankY[side ^ 1][i] + next_step[shot_dir][0], ety = field->tankX[side ^ 1][i] + next_step[shot_dir][1];
						if (etx == tx) shot_dir = ety < ty ? 3 : 2;
						else shot_dir = etx < tx ? 1 : 0;
						temp_action[tank_id] = shot_dir + 4;
						my_action[tank_id] = shot_dir + 4;
						if (shoot_friend(side, tank_id, fx, fy))
						{
							my_action[tank_id] = -2; temp_action[tank_id] = -1;
						}
						//↑上面是友军重新决策，现已修改
						//↓下方增加了一个else
						else if (min_step_to_base[side][tx][ty] >= min_step_to_base[side ^ 1][field->tankY[side ^ 1][i]][field->tankX[side ^ 1][i]]
							|| GetRandom() <= 0.1) {
							if ((fx != tx || fy != ty) || my_action[tank_id] != my_action[tank_id ^ 1])
								if (min_step_to_base[side][fx][fy] + (my_action[tank_id^1]>=0 && my_action[tank_id]<=3)
									<= min_step_to_base[side ^ 1][field->tankY[side ^ 1][i ^ 1]][field->tankX[side ^ 1][i ^ 1]]) {
									Coordinate cord = shoot_coord(shot_dir, tx, ty);
									if (min_path[side ^ 1][i ^ 1][cord.x][cord.y] == 0 || GetRandom() < 0.1) {
										return my_action[tank_id];
									}
								}
								
						}
						my_action[tank_id] = -2;
					} 
				}
			}
		bool cooperate_attack = false; //合作拆家开关，条件较苛刻
		if (field->inOppositeHalf(0, side) && field->inOppositeHalf(1, side)
			&& field->inOppositeHalf(0, side ^ 1), field->inOppositeHalf(1, side ^ 1)
			&& real_shot_range[side^1][tx][ty]<0.001 && real_shot_range[side^1][fx][fy]<0.001) {
			//双方坦克全在对方半场，且均不在射程内
			cooperate_attack = true;
		}


		double shot_weight[4] = { 0,0,0,0 }; //shoot与move的权重
		bool skip_loop;
		if (!force_move_mode) {
			//分配权重 这个方向是射还是走
			for (int dir = 0; dir < 4; dir++) {
				skip_loop = false;
				int ii = tx + next_step[dir][0], jj = ty + next_step[dir][1], cnt = 0;
				//注：后续版本要添加-->预判对方tank走位

				for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]) {
					if (fx == ii && fy == jj) {
						skip_loop = true;
						break;
					}
					cnt++;
				}
				if (skip_loop || !CoordValid(ii, jj)) continue; //停火，友军！（但似乎依然会误伤友军）
				if (field->gameField[ii][jj] == Brick) {
					//此时射击才有意义
					shot_weight[dir] += 0.6;
					shot_weight[dir] += real_shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]] * (cnt > 1 ? 0.8 : -0.4);
					if (shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]] > 0 && real_shot_range[side ^ 1][tx + next_step[dir][0]][ty + next_step[dir][1]] < 0.0001)
						shot_weight[dir] /= 2.4 + 1.2*GetRandom();
					if (min_path[side][tank_id][ii][jj] == 0) {
						//被射的点不在最短路上（目前这个方法有问题,要修改）
						//if(min_path[side][tank_id^1][ii][jj])shot_weight[dir] /= 3 + (cnt + min_step_to_base[side][ii][jj] - min_step_to_base[side][tx][ty])*GetRandom();
						//else 
						shot_weight[dir] = 0;
					}
					if (cooperate_attack && min_step_to_base[side][tx][ty] >= min_step_to_base[side][fx][fy] && min_path[side][tank_id^1][ii][jj]>0) {
						if (my_action[tank_id ^ 1] < 4 || !InShootRange(fx, fy, ii, jj))
							shot_weight[dir] = 0.7; //合作拆家（未测试）
					}

					if ((side == 0 && ii < fieldHeight / 2) || (side == 1 && ii > fieldHeight / 2))shot_weight[dir] *= 0.9; //己方半场射击概率更低 
					else shot_weight[dir] *= 2; //对方半场的射率更高
					if (shot_range[side ^ 1][ii][jj] > 0) {
						shot_weight[dir] *= 0.3;
					}
						
					int wi = ii, wj = jj;
					//以下：本次射击后，不能在射击方向（与反方向）上进入对方射程
					ii += next_step[dir][0], jj += next_step[dir][1];
					int uc, dc;
					for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir][0], jj += next_step[dir][1]);
					uc = next_step[dir][0] ? ii : jj;
					ii = tx; jj = ty;
					for (; CoordValid(ii, jj) && CanBulletAcross(field->gameField[ii][jj]); ii += next_step[dir ^ 1][0], jj += next_step[dir ^ 1][1]);
					dc = next_step[dir ^ 1][0] ? ii : jj;
					if (uc > dc) std::swap(uc, dc);
					//uc dc: 该方向上，可以射到tank的坐标范围
					for (uc++, dc--; uc <= dc; uc++) {
						if((dir<2&&!ItemIsAccessible(field->gameField[uc][ty])) || (dir>=2&&!ItemIsAccessible(field->gameField[tx][uc]))) continue;
						for (int bias = -1; bias <= 1; bias++) {
							if (dir < 2) {//上下
								if (tx == uc && bias) continue;
								if (uc == wi) continue;
								if (uc > min(tx, wi) && uc < max(tx, wi)) continue;
								if (CoordValid(uc, ty + bias) && ((IsTank(field->gameField[uc][ty + bias]) && GetTankSide(field->gameField[uc][ty + bias]) != side)
									|| HasMultipleTank(field->gameField[uc][ty + bias]))) {
									shot_weight[dir] *= min_step_to_base[side ^ 1][uc][ty + bias] >= min_step_to_base[side ^ 1][uc][ty] ? 0 : 0.8;
									int tid = GetTankID(field->gameField[uc][ty + bias]);
									if (min_step_to_base[side ^ 1][wi][wj]<=min_step_to_base[side^1][uc][ty+bias]
										/*&& !(field->previousActions[field->currentTurn - 1][side^1][tid] > Left)*/ && cnt == 0
										/*&& min_step_to_base[side][tx][ty] + 2>= min_step_to_base[side ^ 1][uc][ty + bias]*/) {
										//预判 守株待兔 准备反杀（目前不完善）

										int ddir = (ty > 4) ? 3 : 2;
										Coordinate shot_target = shoot_coord(ddir, tx, ty);
										if (ty != 4&& (side?(tx<=5):(tx>=3)) && CoordValid(shot_target.x, shot_target.y)
											&& field->gameField[shot_target.x][shot_target.y] == Brick
											&&  (tx==4 ||(ty<4?(shot_target.y<=4):(shot_target.y>=4)))
											&& shot_target.y!=0 && shot_target.y!=8
											&& CanSafelyShoot(ddir, shot_target.x, shot_target.y,tx,ty,side)) {
											my_action[tank_id] = ddir + 4;
											if (!shoot_friend(side, tank_id, fx, fy))
												return my_action[tank_id];
											my_action[tank_id] = -2;
										}
										ddir ^= 1;
										shot_target = shoot_coord(ddir, tx, ty);
										if (ty != 4 && (side ? (tx <= 5) : (tx >= 3)) && CoordValid(shot_target.x, shot_target.y)
											&& field->gameField[shot_target.x][shot_target.y] == Brick
											&& (tx == 4 || (ty < 4 ? (shot_target.y <= 4) : (shot_target.y >= 4)))
											&& shot_target.y != 0 && shot_target.y != 8
											&& GetRandom() < 0.45
											&& CanSafelyShoot(ddir, shot_target.x, shot_target.y, tx, ty, side)) {
											my_action[tank_id] = ddir + 4;
											if (!shoot_friend(side, tank_id, fx, fy))
												return my_action[tank_id];
											my_action[tank_id] = -2;
										}
										return my_action[tank_id] = Stay;
									}
									break;
								}
							}
							else {//左右
								if (ty == uc && bias)continue;
								if (uc == wj) continue;
								if (uc > min(ty, wj) && uc < max(ty, wj)) continue;
								if (CoordValid(tx+bias,uc) && ((IsTank(field->gameField[tx+bias][uc]) && GetTankSide(field->gameField[tx+bias][uc]) != side)
									|| HasMultipleTank(field->gameField[tx + bias][uc]))){
									shot_weight[dir] *= min_step_to_base[side ^ 1][tx + bias][uc] >= min_step_to_base[side ^ 1][tx][uc] ? 0 : 0.8;
									int tid = GetTankID(field->gameField[tx + bias][uc]);
									if (min_step_to_base[side ^ 1][wi][wj]<=min_step_to_base[side ^ 1][tx + bias][uc]
										/*&& !(field->previousActions[field->currentTurn - 1][side ^ 1][tid] > Left)*/ && cnt==0
										/*&& min_step_to_base[side][tx][ty] + 2 >= min_step_to_base[side ^ 1][tx + bias][uc] */) {
										// 预判 守株待兔 准备反杀（目前不完善）
										shot_weight[dir] = 0;
										break;
										//return my_action[tank_id] = Stay;
									}
									break;
								}
							}
						}
						if (shot_weight[dir] == 0) break;
					}
				}
				while (--cnt > 0) shot_weight[dir] *= 0.87; //墙每远一格 概率减小一定倍数
			}
			shot_weight[side] *= 1.2; //前
			shot_weight[side ^ 1] *= 0.8; //后
		}
		//act[dir]<0不考虑 shot_weight==0不考虑
		
		for (int dir = 0; dir < 4; dir++) {
			if (GetRandom() < shot_weight[dir] || !ItemIsAccessible(field->gameField[tx + next_step[dir][0]][ty + next_step[dir][1]], false))
				act[dir] = (1.2 * act[dir]) * shot_weight[dir], shot_weight[dir] = 2;//=2(>1)作为标记供以后判断是移还是射(别中了射击)
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
		double sum = 0, max_p = 0;
		//归一化&前缀和
		for (int i = 0; i < 4; i++)sum += act[i];
		if (sum == 0) return my_action[tank_id] = Stay;
		for (int i = 0; i < 4; i++) { 
			act[i] /= sum;
			if (max_p < act[i]) max_p = act[i]; //获取最大概率
		}
		sum = 0;
		for (int i = 0; i < 4; i++) {
			if (act[i] * 1.2 < max_p) act[i] = 0; //*1.2后还是<最大概率的策略直接忽略
			else sum += act[i];
		}

		for (int i = 0; i < 4; i++) {
			act[i] /= sum;
			if (i > 0) act[i] += act[i - 1];
		}
		sum = GetRandom();
		int ans = Stay;
		for (ans = 0; act[ans] < sum; ans++);
		my_action[tank_id] = ans;


		shot_dir = IsUniqueDir(side, tx, ty);
		if (shot_weight[ans] <= 1.5 && my_action[tank_id^1]==-2) {
			if (ty == 4 && ans >= 2 && (ans + tank_id) % 2 == 1 && (tx - 4)*(side - 0.5) > 0) {
				int gx = tx + next_step[ans][0], gy = ty + next_step[ans][1];
				if (gy == fy && (fx - gx == (side ? 1 : -1)))
					ans ^= 1;
			}
		}


		if (shot_weight[ans] > 1.5) my_action[tank_id] += 4; //若别中的是射击，则方案+4
		else if (min_step_to_base[side][tx][ty] < min_step_to_base[side][tx + next_step[ans][0]][ty + next_step[ans][1]]
			&& real_shot_range[side ^ 1][tx][ty] < real_shot_range[side ^ 1][tx + next_step[ans][0]][ty + next_step[ans][1]] + 0.1 + 0.1 * GetRandom())
			my_action[tank_id] = Stay; //不在射程内且行动后最短路变大，则改为stay
		else if (/*min_step_to_base[side][tx][ty] <= min_step_to_base[side][tx + next_step[ans][0]][ty + next_step[ans][1]] &&*/ stay_for_beat[tank_id])
			my_action[tank_id] = Stay;
		else if(min_step_to_base[side][tx][ty] == min_step_to_base[side][tx + next_step[ans][0]][ty + next_step[ans][1]]
			&& real_shot_range[side ^ 1][tx][ty] < real_shot_range[side ^ 1][tx + next_step[ans][0]][ty + next_step[ans][1]])
			my_action[tank_id] = Stay;
		else if (shot_dir >= 0&& ans==shot_dir && real_shot_range[side^1][tx + next_step[ans][0]][ty + next_step[ans][1]] >0.0001) {
			int tid = -1, count, count_dont_move, count_my_stay;
			for (int i = 0; i < tankPerSide; i++) {
				if (InShootRange(field->tankY[side ^ 1][i], field->tankX[side ^ 1][i], tx + next_step[ans][0], ty + next_step[ans][1])) {
					if (tid >= 0) break;
					tid = i;
				}
			}
			for (count = 1; count <= field->currentTurn - 1 && tid >= 0; count++) {
				if (field->previousActions[field->currentTurn - count][side ^ 1][tid] != Stay) break;
			}
			for (count_dont_move = 1; count_dont_move <= field->currentTurn - 1; count_dont_move++) {
				if (field->previousActions[field->currentTurn - count_dont_move][side][tank_id] <= Left && field->previousActions[field->currentTurn - count_dont_move][side][tank_id]>=Up) break;
			}
			for (count_my_stay = 1; count_my_stay <= field->currentTurn - 1 && tid >= 0; count_my_stay++) {
				if (field->previousActions[field->currentTurn - count_my_stay][side][tank_id] != Stay) break;
			}
			if (tid >= 0 && field->tankY[side ^ 1][tid] == tx && field->tankX[side ^ 1][tid] == ty) {
				
				if ((count > 2 + int(GetRandom()*1.8) && min_step_to_base[side][tx][ty]<=min_step_to_base[side^1][tx][ty]) || Ignore_tankid == tid)
					return my_action[tank_id];

			}
			if (tid >= 0 && (count > 3 + int(GetRandom()*1.7) || count_my_stay >= 25) && count_dont_move > 3 + int(GetRandom()*1.7)) {
				// 3或4回合若对方不动，则忽略
				return my_action[tank_id];
			}
			// El 执行到此处，表明最短路唯一下降前方在敌方射程内，并且一定不会往前走了
				// 由于已经别中move，以下将尝试2次看是否能别中向该方向射击，否则改为Stay
			int try_max_count = 2;
			while (shot_weight[ans] < GetRandom() && try_max_count) {
				try_max_count--;
			}
			if (!try_max_count) {
				my_action[tank_id] = Stay;
			}
			else {
				my_action[tank_id] += 4;
			}
		}
		else if (min_step_to_base[side][tx + next_step[ans][0]][ty + next_step[ans][1]] >= min_step_to_base[side ^ 1][tx + next_step[ans][0]][ty + next_step[ans][1]]) {
			int side_num;
			for (int i = 0; i < tankPerSide; i++) {
				side_num = IsUniqueDir(side ^ 1, field->tankY[side ^ 1][i], field->tankX[side ^ 1][i]);
				if (side_num >= 0 && tx + next_step[ans][0] == field->tankY[side ^ 1][i] + next_step[side_num][0] && ty + next_step[ans][1] == field->tankX[side ^ 1][i] + next_step[side_num][1])
					my_action[tank_id] = Stay;
			}
		}
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
		cout << "===========Real Shoot Range===========\n";
		for (int side = 0; side < 2; side++) {
			cout << "###side = " << side << "###\n";
			for (int i = 0; i < fieldHeight; i++) {
				for (int j = 0; j < fieldWidth; j++) {
					cout << std::setprecision(3) << real_shot_range[side][i][j] << ' ';
				}
				cout << endl;
			}
			cout << endl;
		}
		cout << "===========min_path array===========\n";
		for (int side = 0; side < 2; side++) {
			for (int id = 0; id < tankPerSide; id++) {
				cout << "###(side,tank) = (" << side <<","<< id << ") ###\n";
				for (int i = 0; i < fieldHeight; i++) {
					for (int j = 0; j < fieldWidth; j++) {
						cout << min_path[side][id][i][j] << ' ';
					}
					cout << endl;
				}
				cout << endl;
			}
			
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
	//读入信息
	string data, globaldata;
	TankGame::ReadInput(cin, data, globaldata);
	TankGame::field->DebugPrint();

	//初始化随机种子
	srand((unsigned)time(nullptr));
#ifdef _BOTZONE_ONLINE
	//TankGame::decode_data(data);
#endif
	//预处理，包含了bfs等
	TankGame::pre_process();

	//核心决策
	TankGame::get_stupid_action(0);
	TankGame::generate_shot_range(0);
	TankGame::generate_shot_range(1);
	TankGame::get_stupid_action(1);
	for (int i = 0; i < TankGame::tankPerSide; i++) {
		if (TankGame::my_action[i] == TankGame::Action::Stay && 
			TankGame::temp_action[i] != TankGame::Action::Stay && 
			TankGame::GetRandom() < 0.9)
			TankGame::my_action[i] = TankGame::temp_action[i];
	}

	//防御决策
	//这里有两个点要注意：
	//1 默认是同一边的坦克进行防御，不会跨边进行防御
	//2 目前，进行防御决策的条件是我方坦克到敌方基地的距离，比，敌方（同边）坦克到我方基地的距离，至少大2；且地方坦克存活
	//这里可以修改。
	int mySide = TankGame::field->mySide;
	for (int tank = 0; tank < TankGame::tankPerSide; tank++)
	{
		int x = TankGame::field->tankX[mySide][tank];
		int y = TankGame::field->tankY[mySide][tank];
		int ex = TankGame::field->tankX[mySide ^ 1][tank ^ 1];
		int ey = TankGame::field->tankY[mySide ^ 1][tank ^ 1];

		if (!TankGame::field->tankAlive[mySide ^ 1][tank ^ 1])
		{
			TankGame::tankStatusAdv[mySide][tank].force_to_defend = false;
			continue;
		}
		//else
		//撤销防御模式
		if (TankGame::min_step_to_base[mySide][y][x] <= TankGame::min_step_to_base[mySide ^ 1][ey][ex] - 2)
		{
			TankGame::tankStatusAdv[mySide][tank].force_to_defend = false;
			continue;
		}
		if ((mySide==0 && y>=5)|| (mySide == 1 && y <= 4))
		{//撤销防御模式，条件是在敌方半场
			TankGame::tankStatusAdv[mySide][tank].force_to_defend = false;
			continue;
		}
		
		//if ((TankGame::min_step_to_base[mySide][y][x] >= TankGame::min_step_to_base[mySide ^ 1][ey][ex] + 1//应sca要求，前4回合特判 
		//	&& TankGame::field->currentTurn < 4))
		//{
		//	TankGame::get_revising_defense_act(tank, tank ^ 1);//防御同边坦克
		//}
		/*else*/ if (TankGame::min_step_to_base[mySide][y][x] >= TankGame::min_step_to_base[mySide ^ 1][ey][ex] + 2)
		//	&& TankGame::field->currentTurn>=4)
		{
			TankGame::get_revising_defense_act(tank, tank ^ 1);//防御同边坦克
			TankGame::tankStatusAdv[mySide][tank].force_to_defend = true;
		}
		//特判
		else if (TankGame::field->currentTurn >= 7 && TankGame::mht_dis(x, y, TankGame::baseX[mySide], TankGame::baseY[mySide]) < 3)
		{
			TankGame::get_revising_defense_act(tank, tank ^ 1);//防御同边坦克
			TankGame::tankStatusAdv[mySide][tank].force_to_defend = true;
		}
		else if(TankGame::tankStatusAdv[mySide][tank].force_to_defend)
			TankGame::get_revising_defense_act(tank, tank ^ 1);//防御同边坦克
	}

	//lcj: ?????
	//任务：历史位置记录 坦克对峙模式
	TankGame::Action act0 = TankGame::Get_My_Action(TankGame::my_action[0] % 4, TankGame::my_action[0] >= 4);
	TankGame::Action act1 = TankGame::Get_My_Action(TankGame::my_action[1] % 4, TankGame::my_action[1] >= 4);
	int side = TankGame::field->mySide;
	
	//以防万一，若生成的策略无效则随机：
	if (!TankGame::field->ActionIsValid(side, 0, act0)) {
		act0 = RandAction(0);
		if (TankGame::GetRandom() < 0.65) act0 = TankGame::Stay;
	}
	if (!TankGame::field->ActionIsValid(side, 1, act1)) {
		act1 = RandAction(1);
		if (TankGame::GetRandom() < 0.65) act1 = TankGame::Stay;
	}

	//输出，结束
	//TankGame::encode_data(data);
	TankGame::SubmitAndExit(act0, act1, data, data);

}

