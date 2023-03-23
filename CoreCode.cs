using ApplicationLog;
using ILOG.Concert;
using ILOG.CPLEX;
using Npgsql;
using System;
using System.Collections.Generic;
using System.Configuration;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace iTDCS_TrainPlan
{
    public class TrainPlanCplexSolver_MinOperCost
    {
        TimeOperationInfo CurTimeOperInfo;
        List<DiagramRoute> AlterRouteList;
        BasicDataOfLine CurLine;
        List<RouteStation> RetyStation;
        int rNum, fNum, mNum, tNum, dNum, sNum, s1Num, eNum, rMaxNum, iLineMinItvl, iLineMaxItvl;//交路数量、开行列车数量、编组数量、研究时间数量、方向数量、车站数量、折返站数量、区间数量、最大运行交路数量
        double c3, c4, transProp, load;//等待时间成本、换乘次数成本、换乘客流占潜在换乘客流的比例、运营成本目标函数所占比重、满载率
        int[] mMaxR, oM, ceMinE, ceMaxE, nM, c1M, c2M, mM;//交路允许最大编组数数组、区间最大断面客流数组、各编组运力数组、区间最小通过列车数量数组、区间通过列车数量数组、编组列车数量数组、固定成本、变动成本、编组情况
        int[,] rRunRD, pSS, coverRS, pR2, coverRE, rTurnRD, pMaxE;//不同交路方向运行时间、OD客流数组、交路覆盖车站数组、交路折返站覆盖数组、交路覆盖区间数组、不同交路各折返方向终点站的折返时间
        int[,,] sRunS1S1D;//折返站之间的车站运行时间
        double[] rMileR;//交路运行距离包含上下行数组
        List<int[]> rStaIndexListR2;//下行交路的起始和终到折返站索引
        int iDownSrdStaIndex, iUpSrdStaIndex;//上下行基准站索引
        List<List<int>> rTurnRR1;//每一个交路的备选交路可以进行接续的交路
        bool bIsDownDir;//判断下行是否为主要运营方向
        public List<DiagramRoute> DownTrainRouteList { get; set; }
        public List<DiagramRoute> UpTrainRouteList { get; set; }
        public double Z1 { get; set; }
        public double weight { get; set; }
        public TrainPlanCplexSolver_MinOperCost(TimeOperationInfo timeOper, List<DiagramRoute> alterRouteList)
        {
            CurTimeOperInfo = timeOper;
            AlterRouteList = alterRouteList;
            CurLine = timeOper.BelongCapPro.BelongedLine;
            RetyStation = new List<RouteStation>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute alterRoute = AlterRouteList[i];
                if (!RetyStation.Exists(item => item.StationName == alterRoute.StartStationName))
                {
                    RetyStation.Add(alterRoute.RouteStationList[0]);
                }
                if (!RetyStation.Exists(item => item.StationName == alterRoute.LastStationName))
                {
                    RetyStation.Add(alterRoute.RouteStationList[alterRoute.RouteStationList.Count - 1]);
                }
            }
            RetyStation.Sort();
            bIsDownDir = true;
            rTurnRR1 = new List<List<int>>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                List<int> couldTurnRouteIndex = new List<int>();
                for (int j = 0; j < AlterRouteList.Count; j++)
                {
                    DiagramRoute turnRoute = AlterRouteList[j];
                    if (route.StartStationName == turnRoute.StartStationName || route.StartStationName == turnRoute.LastStationName
                        || route.LastStationName == turnRoute.StartStationName || route.LastStationName == turnRoute.LastStationName)
                    {
                        couldTurnRouteIndex.Add(j);
                    }
                }
                rTurnRR1.Add(couldTurnRouteIndex);
            }
            rStaIndexListR2 = new List<int[]>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                int[] staIndexArray = new int[2];
                staIndexArray[0] = RetyStation.FindIndex(item => item.StationName == route.StartStationName);
                staIndexArray[1] = RetyStation.FindIndex(item => item.StationName == route.LastStationName);
                rStaIndexListR2.Add(staIndexArray);
            }
        }

        private void InitialParameter()//初始化参数
        {
            rNum = AlterRouteList.Count;
            tNum = CurTimeOperInfo.TimeSustainSecond;
            fNum = tNum / CurLine.iLineMinItvl;
            string[] mationInfo = CurLine.strVehMation.Split(';');
            mNum = mationInfo.Length;
            dNum = 2;//针对运营方向 0为上行运行方向  1为下行运行方向
            sNum = CurLine.StationList.Count;
            s1Num = RetyStation.Count;
            eNum = CurLine.SectionList.Count;
            rMaxNum = 3;
            c3 = 0;//换乘等待时间成本
            c4 = 0;//换乘次数成本
            //c3 = 28.0 / 3600;//换乘等待时间成本
            //c4 = 2.3;//换乘次数成本
            transProp = 0.5;
            weight = 0.5;//权重
            load = 1;//满载率
            //if (CurLine.iLineType == 2)
            //{
            //    rMaxNum = 4;//预留独立运营交路
            //}
            mMaxR = new int[rNum];
            for (int i = 0; i < rNum; i++)
            {
                mMaxR[i] = AlterRouteList[i].iRouteMation;
            }
            pMaxE = new int[eNum, dNum];
            DateTime dtSrdStaTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "05:30:00");
            DateTime dtSrdLastStaTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + "  " + "07:00:00");
            for (int i = 0; i < eNum; i++)
            {
                BasicDataOfSection section = CurLine.SectionList[i];
                SectionGatherPasFlow downSecPasFlow = section.DownSectionLink.SectionPasFlow;
                SectionGatherPasFlow upSecPasFlow = section.UpSectionLink.SectionPasFlow;
                int iDownPasFlow = 0;
                int iUpPasFlow = 0;
                for (int j = 0; j < downSecPasFlow.SectionPasFlowList_Hour.Count; j++)
                {
                    SectionGatherPasFlowPerHour secDownPasFlowHour = downSecPasFlow.SectionPasFlowList_Hour[j];
                    SectionGatherPasFlowPerHour secUpPasFlowHour = upSecPasFlow.SectionPasFlowList_Hour[j];
                    for (int k = 0; k < secDownPasFlowHour.SectionPasFlowList_Min.Count; k++)
                    {
                        SectionGatherPasFlowMinuteSpan secDownPasFlowMinu = secDownPasFlowHour.SectionPasFlowList_Min[k];
                        SectionGatherPasFlowMinuteSpan secUpPasFlowMinu = secUpPasFlowHour.SectionPasFlowList_Min[k];
                        if (secDownPasFlowMinu.FluxStartDateTime >= dtSrdStaTime && secDownPasFlowMinu.FluxLastDateTime <= dtSrdLastStaTime)
                        {
                            iDownPasFlow += secDownPasFlowMinu.PassengerNum;
                            iUpPasFlow += secUpPasFlowMinu.PassengerNum;
                        }
                    }
                }
                double iAddTimeLength = section.dDownRunTime + section.DownTerminalStation.iDownStopTime;
                dtSrdStaTime = dtSrdStaTime.AddSeconds(iAddTimeLength);
                dtSrdLastStaTime = dtSrdLastStaTime.AddSeconds(iAddTimeLength);
                pMaxE[i, 0] = iUpPasFlow;
                pMaxE[i, 1] = iDownPasFlow;
                //Debug.WriteLine(pMaxE[i]);
            }
            mM = new int[mNum];
            for (int i = 0; i < mNum; i++)
            {
                mM[i] = Convert.ToInt32(mationInfo[i]);
            }
            oM = new int[mNum];
            string[] capacityInfo = CurLine.strVehicleCapacity.Split(';');
            for (int i = 0; i < mNum; i++)
            {
                oM[i] = Convert.ToInt32(capacityInfo[i]);
            }
            ceMinE = new int[eNum];
            for (int i = 0; i < eNum; i++)
            {
                ceMinE[i] = tNum / 600;
            }
            ceMaxE = new int[eNum];
            for (int i = 0; i < eNum; i++)
            {
                ceMaxE[i] = tNum / CurLine.iLineMinItvl;
            }
            nM = new int[mNum];
            for (int i = 0; i < mNum; i++)
            {
                if (i == 0)
                {
                    //nM[i] = 29;
                    nM[i] = 50;
                }
                else
                {
                    nM[i] = 50;
                    //nM[i] = 31;
                }
            }
            rRunRD = new int[rNum, dNum];
            for (int i = 0; i < rNum; i++)//不需要包含始末站的停站时间
            {
                DiagramRoute downRoute = AlterRouteList[i];
                int iDownTime = 0;
                int iUpTime = 0;
                bool bIsStart = false;
                for (int k = 0; k < CurTimeOperInfo.TimeStaStopScale.StationStopTimeList.Count; k++)
                {
                    StationStopTime staStopTime = CurTimeOperInfo.TimeStaStopScale.StationStopTimeList[k];
                    SectionRunTime secRunTime = null;
                    if (k < CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList.Count)
                    {
                        secRunTime = CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList[k];
                    }
                    if (staStopTime.StationName == downRoute.StartStationName)
                    {
                        bIsStart = true;
                        if (secRunTime != null)
                        {
                            iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                            iUpTime += Convert.ToInt32(secRunTime.UpRunTime);

                        }
                    }
                    else if (bIsStart)
                    {
                        iDownTime += Convert.ToInt32(staStopTime.DownStopTime);
                        iUpTime += Convert.ToInt32(staStopTime.UpStopTime);
                        if (secRunTime != null)
                        {
                            iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                            iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                        }
                        if (staStopTime.StationName == downRoute.LastStationName)
                        {
                            iDownTime -= Convert.ToInt32(staStopTime.DownStopTime);
                            iUpTime -= Convert.ToInt32(staStopTime.UpStopTime);
                            if (secRunTime != null)
                            {
                                iDownTime -= Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime -= Convert.ToInt32(secRunTime.UpRunTime);
                            }
                            break;
                        }
                    }
                }
                rRunRD[i, 0] = Convert.ToInt32(iDownTime);
                rRunRD[i, 1] = Convert.ToInt32(iUpTime);
            }
            sRunS1S1D = new int[s1Num, s1Num, dNum];
            for (int i = 0; i < s1Num; i++)//需要包含第二个折返站的停站时间 用以计算列车出发时刻标准化
            {
                RouteStation startSta = RetyStation[i];
                for (int j = i + 1; j < s1Num; j++)
                {
                    RouteStation endSta = RetyStation[j];
                    int iDownTime = 0;
                    int iUpTime = 0;
                    bool bIsStart = false;
                    for (int k = 0; k < CurTimeOperInfo.TimeStaStopScale.StationStopTimeList.Count; k++)
                    {
                        StationStopTime staStopTime = CurTimeOperInfo.TimeStaStopScale.StationStopTimeList[k];
                        SectionRunTime secRunTime = null;
                        if (k < CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList.Count)
                        {
                            secRunTime = CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList[k];
                        }
                        if (staStopTime.StationName == startSta.StationName)
                        {
                            bIsStart = true;
                            if (secRunTime != null)
                            {
                                iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                            }
                        }
                        else if (bIsStart)
                        {
                            iDownTime += Convert.ToInt32(staStopTime.DownStopTime);
                            iUpTime += Convert.ToInt32(staStopTime.UpStopTime);
                            if (secRunTime != null)
                            {
                                iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                            }
                            if (staStopTime.StationName == endSta.StationName)
                            {
                                if (secRunTime != null)
                                {
                                    iDownTime -= Convert.ToInt32(secRunTime.DownRunTime);
                                    iUpTime -= Convert.ToInt32(secRunTime.UpRunTime);
                                }
                                break;
                            }
                        }
                    }
                    sRunS1S1D[i, j, 0] = iUpTime;
                    sRunS1S1D[i, j, 1] = iDownTime;
                }
            }
            pSS = new int[sNum, sNum];
            List<AFCPassengerDataStructure> odPasDataList = DataHandler.GetAFCPassengerDataFromOra(CurTimeOperInfo);
            for (int i = 0; i < sNum; i++)
            {
                for (int j = 0; j < sNum; j++)
                {
                    string oriStaName = CurLine.StationList[i].strStationName;
                    string desStaName = CurLine.StationList[j].strStationName;
                    int iPasNum = 0;
                    for (int k = 0; k < odPasDataList.Count; k++)
                    {
                        AFCPassengerDataStructure odPas = odPasDataList[k];
                        if (odPas.OriStationName == oriStaName && odPas.DesStationName == desStaName)
                        {
                            iPasNum++;
                        }
                    }
                    pSS[i, j] = iPasNum;
                }
            }
            coverRS = new int[rNum, sNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                for (int j = 0; j < sNum; j++)
                {
                    string strStaName = CurLine.StationList[j].strStationName;
                    if (route.RouteStationList.Exists(item => item.StationName == strStaName))
                    {
                        coverRS[i, j] = 1;
                    }
                    else
                    {
                        coverRS[i, j] = 0;
                    }
                }
            }
            pR2 = new int[rNum, 2];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                int iStartStaIndex = CurLine.StationList.FindIndex(item => item.strStationName == route.StartStationName);
                int iLastStaIndex = CurLine.StationList.FindIndex(item => item.strStationName == route.LastStationName);
                int iStartStaPasNum = 0;
                int iEndStaPasNum = 0;
                for (int j = iStartStaIndex; j <= iLastStaIndex; j++)
                {
                    for (int k = 0; k < iStartStaIndex; k++)
                    {
                        iStartStaPasNum += pSS[j, k];
                    }
                    for (int k = iLastStaIndex + 1; k < CurLine.StationList.Count; k++)
                    {
                        iEndStaPasNum += pSS[j, k];
                    }
                }
                pR2[i, 0] = iStartStaPasNum;
                pR2[i, 1] = iEndStaPasNum;
            }
            coverRE = new int[rNum, eNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                for (int j = 0; j < eNum; j++)
                {
                    string strDownStartStationName = CurLine.SectionList[j].strDownStartStationName;
                    string strDownEndStationName = CurLine.SectionList[j].strDownTerminalStationName;
                    if (route.RouteStationList.Exists(item => item.StationName == strDownStartStationName) &&
                        route.RouteStationList.Exists(item => item.StationName == strDownEndStationName))
                    {
                        coverRE[i, j] = 1;
                    }
                    else
                    {
                        coverRE[i, j] = 0;
                    }
                }
            }
            rTurnRD = new int[rNum, dNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                RouteStation downLastStation = route.RouteStationList[route.RouteStationList.Count - 1];
                RouteStation upLastStation = route.RouteStationList[0];
                rTurnRD[i, 0] = upLastStation.iTurnCapacity;
                rTurnRD[i, 1] = downLastStation.iTurnCapacity;
            }
            rMileR = new double[rNum];
            for (int i = 0; i < rNum; i++)
            {
                rMileR[i] = Convert.ToInt32(AlterRouteList[i].dRunKilo * 2 * 0.001);
            }
            c1M = new int[mNum];
            c1M[0] = 450;
            c1M[1] = 340;
            c2M = new int[mNum];
            c2M[0] = 200;
            c2M[1] = 150;
            iLineMinItvl = CurLine.iLineMinItvl;
            iLineMaxItvl = CurLine.iLineMaxItvl;
            iDownSrdStaIndex = 0;
            iUpSrdStaIndex = s1Num - 1;
        }

        public void Calculate()//求解
        {
            try
            {

                Cplex cplex = new Cplex();
                //cplex.SetParam(Cplex.Param.TimeLimit, 60);
                InitialParameter();

                //变量生成
                INumVar[] x = cplex.NumVarArray(rNum, 0.0, 1.0, NumVarType.Bool);
                INumVar[][][] y = new INumVar[rNum][][];
                for (int i = 0; i < rNum; i++)
                {
                    y[i] = new INumVar[fNum][];
                    for (int j = 0; j < fNum; j++)
                    {
                        y[i][j] = cplex.NumVarArray(mNum, 0.0, 1.0, NumVarType.Bool);
                    }
                }
                //INumVar z = cplex.NumVar(0, 855, NumVarType.Int);
                //INumVar[][][][][][] turn = new INumVar[rNum][][][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    turn[i] = new INumVar[fNum][][][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        turn[i][j] = new INumVar[mNum][][][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            turn[i][j][k] = new INumVar[dNum][][];
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[i].Count;
                //                turn[i][j][k][ki] = new INumVar[turnRouteNum][];
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    turn[i][j][k][ki][kj] = cplex.NumVarArray(fNum, 0.0, 1.0, NumVarType.Bool);
                //                }
                //            }
                //        }
                //    }
                //}
                //INumVar[] wS = cplex.NumVarArray(sNum, 0.0, double.MaxValue, NumVarType.Float);//乘客等待时间
                //INumVar h = cplex.NumVar(iLineMinItvl, iLineMaxItvl, NumVarType.Int);
                //INumVar[][][][] liner1 = new INumVar[rNum][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    liner1[i] = new INumVar[fNum][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        liner1[i][j] = new INumVar[mNum][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            liner1[i][j][k] = cplex.NumVarArray(sNum, 0.0, double.MaxValue, NumVarType.Float);
                //        }
                //    }
                //}
                //INumVar[][][] liner2 = new INumVar[rNum][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    liner2[i] = new INumVar[fNum][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        liner2[i][j] = cplex.NumVarArray(mNum, 0.0, double.MaxValue, NumVarType.Float);
                //    }
                //}

                #region 目标函数
                //z11固定成本
                //INumExpr z11 = cplex.NumExpr();
                //INumExpr[] yM = new INumExpr[mNum];//列车数量计算 中间变量
                //for (int i = 0; i < mNum; i++)
                //{
                //    yM[i] = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            yM[i] = cplex.Sum(yM[i], y[j][k][i]);
                //        }
                //    }
                //}
                //INumExpr[] turnM = new INumExpr[mNum];//列车数量计算 中间变量
                //for (int i = 0; i < mNum; i++)
                //{
                //    turnM[i] = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[j].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnM[i] = cplex.Sum(turnM[i], turn[j][k][i][ki][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < mNum; i++)
                //{
                //    z11 = cplex.Sum(z11, cplex.Prod(c1M[i], cplex.Diff(cplex.Prod(2, yM[i]), turnM[i])));
                //}
                //z12运营成本
                INumExpr z12 = cplex.NumExpr();
                for (int i = 0; i < mNum; i++)
                {
                    INumExpr mZ12 = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        INumExpr rTrainCost = cplex.NumExpr();
                        for (int k = 0; k < fNum; k++)
                        {
                            rTrainCost = cplex.Sum(rTrainCost, y[j][k][i]);
                        }
                        rTrainCost = cplex.Prod(rMileR[j], rTrainCost);
                        mZ12 = cplex.Sum(mZ12, rTrainCost);
                    }
                    mZ12 = cplex.Prod(c2M[i], mZ12);
                    z12 = cplex.Sum(z12, mZ12);
                }
                //计算目标函数z1
                //INumExpr z1 = cplex.Prod(weight, cplex.Sum(z11, z12));
                INumExpr z1 = cplex.Prod(weight, z12);
                //z21 乘客始发等待时间
                //INumExpr z21 = cplex.NumExpr();
                //int[] pS = new int[sNum];
                //for (int i = 0; i < sNum; i++)
                //{
                //    for (int j = 0; j < sNum; j++)
                //    {
                //        pS[i] += pSS[i, j];
                //    }
                //}
                //z21 = cplex.Sum(z21, cplex.Prod(c3, cplex.ScalProd(pS, wS)));
                //z22 乘客换乘等待时间
                //INumExpr z22 = cplex.NumExpr();
                //for (int i = 0; i < rNum; i++)
                //{
                //    int pR = 0;
                //    for (int j = 0; j < 2; j++)
                //    {
                //        pR += pR2[i, j];
                //    }
                //    z22 = cplex.Sum(z22, cplex.Prod(x[i], pR));
                //}
                //z22 = cplex.Prod(c4 * transProp, z22);
                //计算目标函数z2
                //INumExpr z2 = cplex.Prod(1 - weight, cplex.Sum(z21, z22));
                //总目标函数z
                //INumExpr obj = cplex.Sum(z1, z2);
                cplex.AddMinimize(z1);
                #endregion

                #region  222930
                //式5 车站覆盖约束
                int iCnstrNum = 0;
                //for (int i = 0; i < sNum; i++)
                //{
                //    INumExpr sCoverLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        sCoverLimit = cplex.Sum(sCoverLimit, cplex.Prod(coverRS[j, i], x[j]));
                //    }
                //    cplex.AddGe(sCoverLimit, 1);
                //    iCnstrNum++;
                //}
                //式6 断面覆盖约束
                //for (int i = 0; i < eNum; i++)
                //{
                //    INumExpr eCoverLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        eCoverLimit = cplex.Sum(eCoverLimit, cplex.Prod(coverRE[j, i], x[j]));
                //    }
                //    cplex.AddGe(eCoverLimit, 1);
                //    iCnstrNum++;
                //}
                //式7 交路运营数量约束
                INumExpr roueNumLimit = cplex.NumExpr();
                for (int i = 0; i < rNum; i++)
                {
                    roueNumLimit = cplex.Sum(roueNumLimit, x[i]);
                }
                cplex.AddLe(roueNumLimit, rMaxNum);
                iCnstrNum++;
                //式8  交路编组数量约束 新增至少一个八编交路被选择
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            cplex.AddLe(cplex.Prod(y[i][j][k], mM[k]), mMaxR[i]);
                //            iCnstrNum++;
                //        }
                //    }
                //}
                //INumExpr mationLimit = cplex.NumExpr();
                //for (int i = 0; i < rNum; i++)
                //{
                //    if (mMaxR[i]== 8)
                //    {
                //        mationLimit = cplex.Sum(x[i], mationLimit);
                //    }
                //}
                //cplex.AddGe(mationLimit,1 );
                //iCnstrNum++;
                //式9 断面运力约束
                for (int i = 0; i < eNum; i++)
                {
                    INumExpr eUpCapLimit = cplex.NumExpr();
                    INumExpr eDownCapLimit = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        if (coverRE[j, i] == 1)
                        {
                            for (int k = 0; k < mNum; k++)
                            {
                                INumExpr mUpTrainCost = cplex.NumExpr();
                                INumExpr mDownTrainCost = cplex.NumExpr();
                                for (int ki = 0; ki < fNum; ki++)
                                {
                                    mUpTrainCost = cplex.Sum(mUpTrainCost, y[j][ki][k]);
                                    mDownTrainCost = cplex.Sum(mDownTrainCost, y[j][ki][k]);
                                }
                                mUpTrainCost = cplex.Prod(oM[k], mUpTrainCost);
                                eUpCapLimit = cplex.Sum(eUpCapLimit, mUpTrainCost);
                                mDownTrainCost = cplex.Prod(oM[k], mDownTrainCost);
                                eDownCapLimit = cplex.Sum(eDownCapLimit, mDownTrainCost);
                            }
                        }
                    }
                    eUpCapLimit = cplex.Prod(load, eUpCapLimit);
                    eDownCapLimit = cplex.Sum(load, eDownCapLimit);
                    cplex.AddGe(eUpCapLimit, pMaxE[i, 0]);
                    cplex.AddGe(eDownCapLimit, pMaxE[i, 1]);
                    iCnstrNum++;
                }
                //式10 线路通过能力约束
                for (int i = 0; i < eNum; i++)
                {
                    INumExpr eLineCapLimit = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        if (coverRE[j, i] == 1)
                        {
                            for (int k = 0; k < fNum; k++)
                            {
                                for (int ki = 0; ki < mNum; ki++)
                                {
                                    eLineCapLimit = cplex.Sum(eLineCapLimit, y[j][k][ki]);
                                }
                            }
                        }
                    }
                    cplex.AddLe(eLineCapLimit, ceMaxE[i]);
                    iCnstrNum++;
                    cplex.AddGe(eLineCapLimit, ceMinE[i]);
                    iCnstrNum++;
                }
                //式12 运用车数量约束
                //for (int i = 0; i < mNum; i++)
                //{
                //    INumExpr vehNumLimit = cplex.Diff(cplex.Prod(2, yM[i]), turnM[i]);
                //    cplex.AddLe(vehNumLimit, nM[i]);
                //    iCnstrNum++;
                //}
                //式15 接续唯一性约束
                //for (int i = 0; i < fNum; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr turnLimit = cplex.NumExpr();
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnLimit = cplex.Sum(turnLimit, turn[k][i][ki][j][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddLe(turnLimit, 1);
                //        iCnstrNum++;
                //    }
                //}
                //式16 接续唯一性约束
                //for (int i = 0; i < fNum; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr connLimit = cplex.NumExpr();
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        connLimit = cplex.Sum(connLimit, turn[k][kk][ki][j][kj][i]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddLe(connLimit, 1);
                //        iCnstrNum++;
                //    }
                //}
                //式17 折返关系之间的约束
                //for (int i = 0; i < fNum - 1; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr turnExpr = cplex.NumExpr();//折返关系之间的约束
                //        INumExpr behTurnExpr = cplex.NumExpr();//折返关系之间的约束
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnExpr = cplex.Sum(turnExpr, turn[k][i][ki][j][kj][kk]);
                //                        behTurnExpr = cplex.Sum(behTurnExpr, turn[k][i + 1][ki][j][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddGe(turnExpr, behTurnExpr);
                //        iCnstrNum++;
                //    }
                //}
                //式18 式19  式22 式23 折返关系之间的约束
                //int iM1 = int.MaxValue;
                //int iM2 = int.MaxValue;
                //INumExpr[][][][] depTimeRFMD = new INumExpr[rNum][][][];
                //INumExpr[][][][] arrTimeRFMD = new INumExpr[rNum][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    depTimeRFMD[i] = new INumExpr[fNum][][];
                //    arrTimeRFMD[i] = new INumExpr[fNum][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        depTimeRFMD[i][j] = new INumExpr[mNum][];
                //        arrTimeRFMD[i][j] = new INumExpr[mNum][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            depTimeRFMD[i][j][k] = new INumExpr[dNum];
                //            arrTimeRFMD[i][j][k] = new INumExpr[dNum];
                //            INumExpr depTime = cplex.NumExpr();//列车i 运行方向为d 的出发时间表达式
                //            INumExpr arrTime = cplex.NumExpr();//列车i 运行方向为d 的出发时间表达式
                //            if (bIsDownDir)//如果下行为主要运营方向
                //            {
                //                depTimeRFMD[i][j][k][1] = cplex.Sum(cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //                depTimeRFMD[i][j][k][0] = cplex.Sum(z, cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //            }
                //            else//如果上行为主要运营方向
                //            {
                //                depTimeRFMD[i][j][k][0] = cplex.Sum(cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //                depTimeRFMD[i][j][k][1] = cplex.Sum(z, cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < rNum; i++)//根据基准站索引更新列车发车时间 与到达时间
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            int iDownStartStaIndex = rStaIndexListR2[i][0];
                //            int iDownEndStaIndex = rStaIndexListR2[i][1];
                //            depTimeRFMD[i][j][k][1] = cplex.Sum(depTimeRFMD[i][j][k][1], sRunS1S1D[iDownSrdStaIndex, iDownStartStaIndex, 1]);
                //            depTimeRFMD[i][j][k][0] = cplex.Sum(depTimeRFMD[i][j][k][0], sRunS1S1D[iUpSrdStaIndex, iDownEndStaIndex, 0]);
                //            arrTimeRFMD[i][j][k][1] = cplex.Sum(depTimeRFMD[i][j][k][1], rRunRD[i, 1]);
                //            arrTimeRFMD[i][j][k][0] = cplex.Sum(depTimeRFMD[i][j][k][0], rRunRD[i, 0]);
                //        }
                //    }
                //}
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int iAlterTurnRouteNum = rTurnRR1[i].Count;
                //                for (int kj = 0; kj < iAlterTurnRouteNum; kj++)
                //                {
                //                    int iAlterRouteIndex = rTurnRR1[i][kj];
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        cplex.AddGe(cplex.Sum(cplex.Diff(depTimeRFMD[iAlterRouteIndex][kk][k][1 - ki], arrTimeRFMD[i][j][k][ki]), cplex.Prod(iM1, cplex.Diff(1, turn[i][j][k][ki][kj][kk]))), rTurnRD[i, ki]);
                //                        iCnstrNum++;
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}
                //式20 变量x与y之间的约束
                for (int i = 0; i < rNum; i++)
                {
                    INumExpr yxLimit = cplex.NumExpr();
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            yxLimit = cplex.Sum(yxLimit, y[i][j][k]);
                        }
                    }
                    cplex.AddLe(yxLimit, cplex.Prod(fNum, x[i]));
                    iCnstrNum++;
                }
                //新增约束 所有列车开行交路不能超过1
                for (int i = 0; i < fNum; i++)
                {
                    INumExpr trainNumLimit = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            trainNumLimit = cplex.Sum(trainNumLimit, y[j][i][k]);
                        }
                    }
                    cplex.AddLe(trainNumLimit, 1);
                    iCnstrNum++;
                }
                //式21 变量y之间的约束
                for (int i = 0; i < fNum - 1; i++)
                {
                    INumExpr trainNum = cplex.NumExpr();
                    INumExpr behTrainNum = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            trainNum = cplex.Sum(trainNum, y[j][i][k]);
                            behTrainNum = cplex.Sum(behTrainNum, y[j][i + 1][k]);
                        }
                    }
                    cplex.AddGe(trainNum, behTrainNum);
                }
                //线性化的约束   式29-33
                //int iM3 = int.MaxValue;
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < sNum; ki++)
                //            {
                //                cplex.AddLe(liner1[i][j][k][ki], cplex.Prod(iM3 * coverRS[i, ki], y[i][j][k]));
                //                iCnstrNum++;
                //                cplex.AddLe(liner1[i][j][k][ki], wS[ki]);
                //                iCnstrNum++;
                //                cplex.AddGe(liner1[i][j][k][ki], cplex.Diff(wS[ki], cplex.Prod(iM3, cplex.Diff(1, cplex.Prod(coverRS[i, ki], y[i][j][k])))));
                //                iCnstrNum++;
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < sNum; i++)
                //{
                //    INumExpr waitTimeLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                waitTimeLimit = cplex.Sum(waitTimeLimit, liner1[j][k][ki][i]);
                //            }
                //        }
                //    }
                //    int iPasNum = 0;
                //    for (int j = 0; j < sNum; j++)
                //    {
                //        iPasNum += pSS[i, j];
                //    }
                //    cplex.AddEq(waitTimeLimit, iPasNum * tNum);
                //    iCnstrNum++;
                //}
                //线性化的约束   式34-38
                //int iM4 = int.MaxValue;
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            cplex.AddLe(liner2[i][j][k], cplex.Prod(iM4, y[i][j][k]));
                //            iCnstrNum++;
                //            cplex.AddLe(liner2[i][j][k], h);
                //            iCnstrNum++;
                //            cplex.AddGe(liner2[i][j][k], cplex.Diff(h, cplex.Prod(iM4, cplex.Diff(1, y[i][j][k]))));
                //            iCnstrNum++;
                //        }
                //    }
                //}
                //INumExpr headwayLimit = cplex.NumExpr();//间隔等式约束
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            headwayLimit = cplex.Sum(headwayLimit, liner2[i][j][k]);
                //        }
                //    }
                //}
                //cplex.AddEq(headwayLimit, tNum);
                //iCnstrNum++;
                //新增折返约束 要保持到达列车与出发列车的折返站是一致的  看要不要补充到论文里
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int iTurnRCount = rTurnRR1[i].Count;
                //                for (int kj = 0; kj < iTurnRCount; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        cplex.AddEq(cplex.Prod(turn[i][j][k][ki][kj][kk], rStaIndexListR2[i][ki]), cplex.Prod(turn[i][j][k][ki][kj][kk], rStaIndexListR2[kj][1 - ki]));
                //                        iCnstrNum++;
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}
                #endregion

                if (cplex.Solve())
                {
                    DownTrainRouteList = new List<DiagramRoute>();
                    UpTrainRouteList = new List<DiagramRoute>();

                    if (cplex.GetStatus().Equals(Cplex.Status.Infeasible))
                    {
                        Debug.WriteLine("No Solution");
                        return;
                    }
                    Z1 = cplex.ObjValue;
                    // Print results
                    Debug.WriteLine("Solution status = " + cplex.GetStatus());
                    Debug.WriteLine("Cost:" + cplex.ObjValue);

                    Debug.WriteLine("交路选择:");
                    for (int i = 0; i < rNum; i++)
                    {
                        double iRouteSelect = cplex.GetValue(x[i]);
                        if (iRouteSelect == 1)
                        {
                            string routeInfo = AlterRouteList[i].RouteName;
                            Debug.WriteLine("(" + i + ") " + routeInfo);
                        }
                    }

                    Debug.WriteLine("列车开行:");
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int i = 0; i < rNum; i++)
                        {
                            for (int k = 0; k < mNum; k++)
                            {
                                double trainSelect = cplex.GetValue(y[i][j][k]);
                                if (trainSelect != 0)
                                {
                                    string routeInfo = AlterRouteList[i].RouteName;

                                    DownTrainRouteList.Add(AlterRouteList[i]);
                                    UpTrainRouteList.Add(AlterRouteList[i].ConverseRoute);
                                    Debug.WriteLine(routeInfo + "  第" + j + "列  编组" + mM[k]);
                                }
                            }
                        }
                    }



                    //目标函数费用以及运力运量匹配情况
                    double totalCost = 0;
                    for (int i = 0; i < mNum; i++)
                    {
                        double mZ12 = 0;
                        for (int j = 0; j < rNum; j++)
                        {
                            double rTrainCost = 0;
                            for (int k = 0; k < fNum; k++)
                            {
                                rTrainCost += cplex.GetValue(y[j][k][i]);
                            }
                            rTrainCost = rMileR[j] * rTrainCost;
                            mZ12 += rTrainCost;
                        }
                        mZ12 = mZ12 * c2M[i];
                        totalCost += mZ12;
                    }
                    Debug.WriteLine("目标函数计算值:" + totalCost * weight);

                    Debug.WriteLine("上行运力运量匹配：");
                    for (int i = 0; i < eNum; i++)
                    {
                        double eTrainCap = 0;
                        for (int j = 0; j < rNum; j++)
                        {
                            if (coverRE[j, i] == 1)
                            {
                                for (int k = 0; k < fNum; k++)
                                {
                                    for (int ki = 0; ki < mNum; ki++)
                                    {
                                        double trainSelect_Up = cplex.GetValue(y[j][k][ki]);
                                        eTrainCap += trainSelect_Up * oM[ki];
                                    }
                                }
                            }
                        }
                        string strInfo = CurLine.SectionList[i].strUpSectionName + "  " + pMaxE[i, 0] + "  " + eTrainCap;
                        Debug.WriteLine(strInfo);
                    }

                    Debug.WriteLine("下行运力运量匹配：");
                    for (int i = 0; i < eNum; i++)
                    {
                        double eTrainCap = 0;
                        for (int j = 0; j < rNum; j++)
                        {
                            if (coverRE[j, i] == 1)
                            {
                                for (int k = 0; k < fNum; k++)
                                {
                                    for (int ki = 0; ki < mNum; ki++)
                                    {
                                        double trainSelect_Down = cplex.GetValue(y[j][k][ki]);
                                        eTrainCap += trainSelect_Down * oM[ki];
                                    }
                                }
                            }
                        }
                        string strInfo = CurLine.SectionList[i].strDownSectionName + "  " + pMaxE[i, 1] + "  " + eTrainCap;
                        Debug.WriteLine(strInfo);
                    }

                    //手动更改列车运行计划
                    DownTrainRouteList.Clear();
                    UpTrainRouteList.Clear();
                    for (int i = 0; i < 13; i++)
                    {
                        DownTrainRouteList.Add(AlterRouteList[0]);
                        UpTrainRouteList.Add(AlterRouteList[0].ConverseRoute);
                    }
                    double dTrainCapacity = oM[1] * 13;
                    Z1 = rMileR[0] * 13 * weight * c2M[1];
                    //Debug.WriteLine("偏移量:" + cplex.GetValue(z));

                    //Debug.WriteLine("接续情况:");
                    //int iTurnNum = 0;
                    //for (int i = 0; i < rNum; i++)
                    //{
                    //    for (int j = 0; j < fNum; j++)
                    //    {
                    //        for (int k = 0; k < mNum; k++)
                    //        {
                    //            for (int ki = 0; ki < dNum; ki++)
                    //            {
                    //                for (int kj = 0; kj < rTurnRR1[i].Count; kj++)
                    //                {
                    //                    double[] turnInfo = cplex.GetValues(turn[i][j][k][ki][kj]);
                    //                    for (int kk = 0; kk < fNum; kk++)
                    //                    {
                    //                        if (turnInfo[kk] == 1)
                    //                        {
                    //                            iTurnNum++;
                    //                            string dir = "下行";
                    //                            string reDir = "上行";
                    //                            if (ki == 0)
                    //                            {
                    //                                dir = "上行";
                    //                                reDir = "下行";
                    //                            }
                    //                            string strTurnInfo = AlterRouteList[i].RouteName + "  " + j + "  " + mM[k] + "  " + dir + "——";
                    //                            strTurnInfo += AlterRouteList[rTurnRR1[i][kj]].RouteName + "  " + kk + "  " + mM[k] + "  " + reDir;
                    //                            Debug.WriteLine("(" + iTurnNum + ") " + strTurnInfo);
                    //                        }
                    //                    }
                    //                }
                    //            }
                    //        }
                    //    }
                    //}

                    //Debug.WriteLine("车站乘客候车时间:");
                    //double[] staWaitTime = cplex.GetValues(wS);
                    //for (int i = 0; i < sNum; i++)
                    //{
                    //    string strStaWaitTime = CurLine.StationList[i].strStationName + "  " + staWaitTime[i];
                    //    Debug.WriteLine(strStaWaitTime);
                    //}

                    //Debug.WriteLine("行车间隔:" + cplex.GetValue(h));
                    //针对推荐的运力方案进行
                }

                cplex.End();
            }
            catch (ILOG.Concert.Exception exc)
            {
                Debug.WriteLine("Concert exception '" + exc + "' caught");
            }
        }
    }

    public class TrainPlanCplexSolver_MinOperCost_Dir//只考虑运营成本的双向
    {
        public double Z1 { get; set; }
        public double weight { get; set; }
        public List<DiagramRoute> DownTrainRouteList { get; set; }
        public List<DiagramRoute> UpTrainRouteList { get; set; }
        TimeOperationInfo CurTimeOperInfo;
        List<DiagramRoute> AlterRouteList;
        BasicDataOfLine CurLine;
        List<RouteStation> RetyStation;
        int rNum, fNum, mNum, tNum, dNum, sNum, s1Num, eNum, rMaxNum, iLineMinItvl, iLineMaxItvl;//交路数量、开行列车数量、编组数量、研究时间数量、方向数量、车站数量、折返站数量、区间数量、最大运行交路数量
        double c3, c4, transProp, load;//等待时间成本、换乘次数成本、换乘客流占潜在换乘客流的比例、运营成本目标函数所占比重、满载率
        int[] mMaxR, oM, ceMinE, ceMaxE, nM, c1M, c2M, mM;//交路允许最大编组数数组、区间最大断面客流数组、各编组运力数组、区间最小通过列车数量数组、区间通过列车数量数组、编组列车数量数组、固定成本、变动成本、编组情况
        int[,] rRunRD, pSS, coverRS, pR2, coverRE, rTurnRD, pMaxE;//不同交路方向运行时间、OD客流数组、交路覆盖车站数组、交路折返站覆盖数组、交路覆盖区间数组、不同交路各折返方向终点站的折返时间
        int[,,] sRunS1S1D;//折返站之间的车站运行时间
        double[] rMileR;//交路运行距离包含上下行数组
        List<int[]> rStaIndexListR2;//下行交路的起始和终到折返站索引
        int iDownSrdStaIndex, iUpSrdStaIndex;//上下行基准站索引
        List<List<int>> rTurnRR1;//每一个交路的备选交路可以进行接续的交路
        bool bIsDownDir;//判断下行是否为主要运营方向
        double Z1Cnstr;

        public TrainPlanCplexSolver_MinOperCost_Dir(TimeOperationInfo timeOper, List<DiagramRoute> alterRouteList, double zCnstr)
        {
            CurTimeOperInfo = timeOper;
            AlterRouteList = alterRouteList;
            CurLine = timeOper.BelongCapPro.BelongedLine;
            RetyStation = new List<RouteStation>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute alterRoute = AlterRouteList[i];
                if (!RetyStation.Exists(item => item.StationName == alterRoute.StartStationName))
                {
                    RetyStation.Add(alterRoute.RouteStationList[0]);
                }
                if (!RetyStation.Exists(item => item.StationName == alterRoute.LastStationName))
                {
                    RetyStation.Add(alterRoute.RouteStationList[alterRoute.RouteStationList.Count - 1]);
                }
            }
            RetyStation.Sort();
            bIsDownDir = true;
            rTurnRR1 = new List<List<int>>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                List<int> couldTurnRouteIndex = new List<int>();
                for (int j = 0; j < AlterRouteList.Count; j++)
                {
                    DiagramRoute turnRoute = AlterRouteList[j];
                    if (route.StartStationName == turnRoute.StartStationName || route.StartStationName == turnRoute.LastStationName
                        || route.LastStationName == turnRoute.StartStationName || route.LastStationName == turnRoute.LastStationName)
                    {
                        couldTurnRouteIndex.Add(j);
                    }
                }
                rTurnRR1.Add(couldTurnRouteIndex);
            }
            rStaIndexListR2 = new List<int[]>();
            for (int i = 0; i < AlterRouteList.Count; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                int[] staIndexArray = new int[2];
                staIndexArray[0] = RetyStation.FindIndex(item => item.StationName == route.StartStationName);
                staIndexArray[1] = RetyStation.FindIndex(item => item.StationName == route.LastStationName);
                rStaIndexListR2.Add(staIndexArray);
            }
            Z1Cnstr = zCnstr;
        }

        private void InitialParameter()//初始化参数
        {
            rNum = AlterRouteList.Count;
            tNum = CurTimeOperInfo.TimeSustainSecond;
            fNum = tNum / CurLine.iLineMinItvl;
            string[] mationInfo = CurLine.strVehMation.Split(';');
            mNum = mationInfo.Length;
            dNum = 2;//针对运营方向 0为上行运行方向  1为下行运行方向
            sNum = CurLine.StationList.Count;
            s1Num = RetyStation.Count;
            eNum = CurLine.SectionList.Count;
            rMaxNum = 3;
            c3 = 0;//换乘等待时间成本
            c4 = 0;//换乘次数成本
            //c3 = 28.0 / 3600;//换乘等待时间成本
            //c4 = 2.3;//换乘次数成本
            transProp = 0.5;
            //weight = 0.5;//权重
            load = 1;//满载率
            //if (CurLine.iLineType == 2)
            //{
            //    rMaxNum = 4;//预留独立运营交路
            //}
            mMaxR = new int[rNum];
            for (int i = 0; i < rNum; i++)
            {
                mMaxR[i] = AlterRouteList[i].iRouteMation;
            }
            pMaxE = new int[eNum, dNum];
            DateTime dtSrdStaTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "05:30:00");
            DateTime dtSrdLastStaTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + "  " + "07:00:00");
            for (int i = 0; i < eNum; i++)
            {
                BasicDataOfSection section = CurLine.SectionList[i];
                SectionGatherPasFlow downSecPasFlow = section.DownSectionLink.SectionPasFlow;
                SectionGatherPasFlow upSecPasFlow = section.UpSectionLink.SectionPasFlow;
                int iDownPasFlow = 0;
                int iUpPasFlow = 0;
                for (int j = 0; j < downSecPasFlow.SectionPasFlowList_Hour.Count; j++)
                {
                    SectionGatherPasFlowPerHour secDownPasFlowHour = downSecPasFlow.SectionPasFlowList_Hour[j];
                    SectionGatherPasFlowPerHour secUpPasFlowHour = upSecPasFlow.SectionPasFlowList_Hour[j];
                    for (int k = 0; k < secDownPasFlowHour.SectionPasFlowList_Min.Count; k++)
                    {
                        SectionGatherPasFlowMinuteSpan secDownPasFlowMinu = secDownPasFlowHour.SectionPasFlowList_Min[k];
                        SectionGatherPasFlowMinuteSpan secUpPasFlowMinu = secUpPasFlowHour.SectionPasFlowList_Min[k];
                        if (secDownPasFlowMinu.FluxStartDateTime >= dtSrdStaTime && secDownPasFlowMinu.FluxLastDateTime <= dtSrdLastStaTime)
                        {
                            iDownPasFlow += secDownPasFlowMinu.PassengerNum;
                            iUpPasFlow += secUpPasFlowMinu.PassengerNum;
                        }
                    }
                }
                double iAddTimeLength = section.dDownRunTime + section.DownTerminalStation.iDownStopTime;
                dtSrdStaTime = dtSrdStaTime.AddSeconds(iAddTimeLength);
                dtSrdLastStaTime = dtSrdLastStaTime.AddSeconds(iAddTimeLength);
                pMaxE[i, 0] = iUpPasFlow;
                pMaxE[i, 1] = iDownPasFlow;
                //Debug.WriteLine(pMaxE[i]);
            }
            mM = new int[mNum];
            for (int i = 0; i < mNum; i++)
            {
                mM[i] = Convert.ToInt32(mationInfo[i]);
            }
            oM = new int[mNum];
            string[] capacityInfo = CurLine.strVehicleCapacity.Split(';');
            for (int i = 0; i < mNum; i++)
            {
                oM[i] = Convert.ToInt32(capacityInfo[i]);
            }
            ceMinE = new int[eNum];
            for (int i = 0; i < eNum; i++)
            {
                ceMinE[i] = tNum / 600;
            }
            ceMaxE = new int[eNum];
            for (int i = 0; i < eNum; i++)
            {
                ceMaxE[i] = tNum / CurLine.iLineMinItvl;
            }
            nM = new int[mNum];
            for (int i = 0; i < mNum; i++)
            {
                if (i == 0)
                {
                    nM[i] = 29;
                    //nM[i] = 50;
                }
                else
                {
                    //nM[i] = 50;
                    nM[i] = 31;
                }
            }
            rRunRD = new int[rNum, dNum];
            for (int i = 0; i < rNum; i++)//不需要包含始末站的停站时间
            {
                DiagramRoute downRoute = AlterRouteList[i];
                int iDownTime = 0;
                int iUpTime = 0;
                bool bIsStart = false;
                for (int k = 0; k < CurTimeOperInfo.TimeStaStopScale.StationStopTimeList.Count; k++)
                {
                    StationStopTime staStopTime = CurTimeOperInfo.TimeStaStopScale.StationStopTimeList[k];
                    SectionRunTime secRunTime = null;
                    if (k < CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList.Count)
                    {
                        secRunTime = CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList[k];
                    }
                    if (staStopTime.StationName == downRoute.StartStationName)
                    {
                        bIsStart = true;
                        if (secRunTime != null)
                        {
                            iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                            iUpTime += Convert.ToInt32(secRunTime.UpRunTime);

                        }
                    }
                    else if (bIsStart)
                    {
                        iDownTime += Convert.ToInt32(staStopTime.DownStopTime);
                        iUpTime += Convert.ToInt32(staStopTime.UpStopTime);
                        if (secRunTime != null)
                        {
                            iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                            iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                        }
                        if (staStopTime.StationName == downRoute.LastStationName)
                        {
                            iDownTime -= Convert.ToInt32(staStopTime.DownStopTime);
                            iUpTime -= Convert.ToInt32(staStopTime.UpStopTime);
                            if (secRunTime != null)
                            {
                                iDownTime -= Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime -= Convert.ToInt32(secRunTime.UpRunTime);
                            }
                            break;
                        }
                    }
                }
                rRunRD[i, 0] = Convert.ToInt32(iDownTime);
                rRunRD[i, 1] = Convert.ToInt32(iUpTime);
            }
            sRunS1S1D = new int[s1Num, s1Num, dNum];
            for (int i = 0; i < s1Num; i++)//需要包含第二个折返站的停站时间 用以计算列车出发时刻标准化
            {
                RouteStation startSta = RetyStation[i];
                for (int j = i + 1; j < s1Num; j++)
                {
                    RouteStation endSta = RetyStation[j];
                    int iDownTime = 0;
                    int iUpTime = 0;
                    bool bIsStart = false;
                    for (int k = 0; k < CurTimeOperInfo.TimeStaStopScale.StationStopTimeList.Count; k++)
                    {
                        StationStopTime staStopTime = CurTimeOperInfo.TimeStaStopScale.StationStopTimeList[k];
                        SectionRunTime secRunTime = null;
                        if (k < CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList.Count)
                        {
                            secRunTime = CurTimeOperInfo.TimeSecRunScale.SectionRunTimeList[k];
                        }
                        if (staStopTime.StationName == startSta.StationName)
                        {
                            bIsStart = true;
                            if (secRunTime != null)
                            {
                                iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                            }
                        }
                        else if (bIsStart)
                        {
                            iDownTime += Convert.ToInt32(staStopTime.DownStopTime);
                            iUpTime += Convert.ToInt32(staStopTime.UpStopTime);
                            if (secRunTime != null)
                            {
                                iDownTime += Convert.ToInt32(secRunTime.DownRunTime);
                                iUpTime += Convert.ToInt32(secRunTime.UpRunTime);
                            }
                            if (staStopTime.StationName == endSta.StationName)
                            {
                                if (secRunTime != null)
                                {
                                    iDownTime -= Convert.ToInt32(secRunTime.DownRunTime);
                                    iUpTime -= Convert.ToInt32(secRunTime.UpRunTime);
                                }
                                break;
                            }
                        }
                    }
                    sRunS1S1D[i, j, 0] = iUpTime;
                    sRunS1S1D[i, j, 1] = iDownTime;
                }
            }
            pSS = new int[sNum, sNum];
            List<AFCPassengerDataStructure> odPasDataList = DataHandler.GetAFCPassengerDataFromOra(CurTimeOperInfo);
            for (int i = 0; i < sNum; i++)
            {
                for (int j = 0; j < sNum; j++)
                {
                    string oriStaName = CurLine.StationList[i].strStationName;
                    string desStaName = CurLine.StationList[j].strStationName;
                    int iPasNum = 0;
                    for (int k = 0; k < odPasDataList.Count; k++)
                    {
                        AFCPassengerDataStructure odPas = odPasDataList[k];
                        if (odPas.OriStationName == oriStaName && odPas.DesStationName == desStaName)
                        {
                            iPasNum++;
                        }
                    }
                    pSS[i, j] = iPasNum;
                }
            }
            coverRS = new int[rNum, sNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                for (int j = 0; j < sNum; j++)
                {
                    string strStaName = CurLine.StationList[j].strStationName;
                    if (route.RouteStationList.Exists(item => item.StationName == strStaName))
                    {
                        coverRS[i, j] = 1;
                    }
                    else
                    {
                        coverRS[i, j] = 0;
                    }
                }
            }
            pR2 = new int[rNum, 2];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                int iStartStaIndex = CurLine.StationList.FindIndex(item => item.strStationName == route.StartStationName);
                int iLastStaIndex = CurLine.StationList.FindIndex(item => item.strStationName == route.LastStationName);
                int iStartStaPasNum = 0;
                int iEndStaPasNum = 0;
                for (int j = iStartStaIndex; j <= iLastStaIndex; j++)
                {
                    for (int k = 0; k < iStartStaIndex; k++)
                    {
                        iStartStaPasNum += pSS[j, k];
                    }
                    for (int k = iLastStaIndex + 1; k < CurLine.StationList.Count; k++)
                    {
                        iEndStaPasNum += pSS[j, k];
                    }
                }
                pR2[i, 0] = iStartStaPasNum;
                pR2[i, 1] = iEndStaPasNum;
            }
            coverRE = new int[rNum, eNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                for (int j = 0; j < eNum; j++)
                {
                    string strDownStartStationName = CurLine.SectionList[j].strDownStartStationName;
                    string strDownEndStationName = CurLine.SectionList[j].strDownTerminalStationName;
                    if (route.RouteStationList.Exists(item => item.StationName == strDownStartStationName) &&
                        route.RouteStationList.Exists(item => item.StationName == strDownEndStationName))
                    {
                        coverRE[i, j] = 1;
                    }
                    else
                    {
                        coverRE[i, j] = 0;
                    }
                }
            }
            rTurnRD = new int[rNum, dNum];
            for (int i = 0; i < rNum; i++)
            {
                DiagramRoute route = AlterRouteList[i];
                RouteStation downLastStation = route.RouteStationList[route.RouteStationList.Count - 1];
                RouteStation upLastStation = route.RouteStationList[0];
                rTurnRD[i, 0] = upLastStation.iTurnCapacity;
                rTurnRD[i, 1] = downLastStation.iTurnCapacity;
            }
            rMileR = new double[rNum];
            for (int i = 0; i < rNum; i++)
            {
                rMileR[i] = Convert.ToInt32(AlterRouteList[i].dRunKilo * 0.001);
            }
            c1M = new int[mNum];
            c1M[0] = 450;
            c1M[1] = 340;
            c2M = new int[mNum];
            c2M[0] = 200;
            c2M[1] = 150;
            iLineMinItvl = CurLine.iLineMinItvl;
            iLineMaxItvl = CurLine.iLineMaxItvl;
            iDownSrdStaIndex = 0;
            iUpSrdStaIndex = s1Num - 1;

        }

        public void Calculate()//求解
        {
            //zLimit 表示目标函数限制
            try
            {

                Cplex cplex = new Cplex();
                cplex.SetParam(Cplex.Param.TimeLimit, 180);//限制时间为3分钟
                InitialParameter();

                //变量生成

                INumVar[] x = cplex.NumVarArray(rNum, 0.0, 1.0, NumVarType.Bool);
                INumVar[][][][] y = new INumVar[rNum][][][];
                for (int i = 0; i < rNum; i++)
                {
                    y[i] = new INumVar[fNum][][];
                    for (int j = 0; j < fNum; j++)
                    {
                        y[i][j] = new INumVar[mNum][];
                        for (int k = 0; k < dNum; k++)
                        {
                            y[i][j][k] = cplex.NumVarArray(dNum, 0.0, 1.0, NumVarType.Bool);
                        }
                    }
                }
                INumVar z = cplex.NumVar(0, double.MaxValue);//目标函数值约束
                //INumVar[][][][][][] turn = new INumVar[rNum][][][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    turn[i] = new INumVar[fNum][][][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        turn[i][j] = new INumVar[mNum][][][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            turn[i][j][k] = new INumVar[dNum][][];
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[i].Count;
                //                turn[i][j][k][ki] = new INumVar[turnRouteNum][];
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    turn[i][j][k][ki][kj] = cplex.NumVarArray(fNum, 0.0, 1.0, NumVarType.Bool);
                //                }
                //            }
                //        }
                //    }
                //}
                //INumVar[] wS = cplex.NumVarArray(sNum, 0.0, double.MaxValue, NumVarType.Float);//乘客等待时间
                //INumVar h = cplex.NumVar(iLineMinItvl, iLineMaxItvl, NumVarType.Int);
                //INumVar[][][][] liner1 = new INumVar[rNum][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    liner1[i] = new INumVar[fNum][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        liner1[i][j] = new INumVar[mNum][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            liner1[i][j][k] = cplex.NumVarArray(sNum, 0.0, double.MaxValue, NumVarType.Float);
                //        }
                //    }
                //}
                //INumVar[][][] liner2 = new INumVar[rNum][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    liner2[i] = new INumVar[fNum][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        liner2[i][j] = cplex.NumVarArray(mNum, 0.0, double.MaxValue, NumVarType.Float);
                //    }
                //}

                #region 目标函数
                //z11固定成本
                //INumExpr z11 = cplex.NumExpr();
                //INumExpr[] yM = new INumExpr[mNum];//列车数量计算 中间变量
                //for (int i = 0; i < mNum; i++)
                //{
                //    yM[i] = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            yM[i] = cplex.Sum(yM[i], y[j][k][i]);
                //        }
                //    }
                //}
                //INumExpr[] turnM = new INumExpr[mNum];//列车数量计算 中间变量
                //for (int i = 0; i < mNum; i++)
                //{
                //    turnM[i] = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[j].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnM[i] = cplex.Sum(turnM[i], turn[j][k][i][ki][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < mNum; i++)
                //{
                //    z11 = cplex.Sum(z11, cplex.Prod(c1M[i], cplex.Diff(cplex.Prod(2, yM[i]), turnM[i])));
                //}
                //z12运营成本
                INumExpr z12 = cplex.NumExpr();
                for (int i = 0; i < mNum; i++)
                {
                    INumExpr mZ12 = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        INumExpr rTrainCost = cplex.NumExpr();
                        for (int k = 0; k < fNum; k++)
                        {
                            rTrainCost = cplex.Sum(rTrainCost, y[j][k][i][0]);
                            rTrainCost = cplex.Sum(rTrainCost, y[j][k][i][1]);
                        }
                        rTrainCost = cplex.Prod(rMileR[j], rTrainCost);
                        mZ12 = cplex.Sum(mZ12, rTrainCost);
                    }
                    mZ12 = cplex.Prod(c2M[i], mZ12);
                    z12 = cplex.Sum(z12, mZ12);
                }
                //计算目标函数z1
                //INumExpr z1 = cplex.Prod(weight, cplex.Sum(z11, z12));
                INumExpr z1 = cplex.Prod(weight, z12);
                //z21 乘客始发等待时间
                //INumExpr z21 = cplex.NumExpr();
                //int[] pS = new int[sNum];
                //for (int i = 0; i < sNum; i++)
                //{
                //    for (int j = 0; j < sNum; j++)
                //    {
                //        pS[i] += pSS[i, j];
                //    }
                //}
                //z21 = cplex.Sum(z21, cplex.Prod(c3, cplex.ScalProd(pS, wS)));
                //z22 乘客换乘等待时间
                //INumExpr z22 = cplex.NumExpr();
                //for (int i = 0; i < rNum; i++)
                //{
                //    int pR = 0;
                //    for (int j = 0; j < 2; j++)
                //    {
                //        pR += pR2[i, j];
                //    }
                //    z22 = cplex.Sum(z22, cplex.Prod(x[i], pR));
                //}
                //z22 = cplex.Prod(c4 * transProp, z22);
                //计算目标函数z2
                //INumExpr z2 = cplex.Prod(1 - weight, cplex.Sum(z21, z22));
                //总目标函数z
                //INumExpr obj = cplex.Sum(z1, z2);
                cplex.AddMinimize(z1);
                #endregion

                #region  222930
                //式5 车站覆盖约束
                int iCnstrNum = 0;
                //for (int i = 0; i < sNum; i++)
                //{
                //    INumExpr sCoverLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        sCoverLimit = cplex.Sum(sCoverLimit, cplex.Prod(coverRS[j, i], x[j]));
                //    }
                //    cplex.AddGe(sCoverLimit, 1);
                //    iCnstrNum++;
                //}
                //式6 断面覆盖约束
                //for (int i = 0; i < eNum; i++)
                //{
                //    INumExpr eCoverLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        eCoverLimit = cplex.Sum(eCoverLimit, cplex.Prod(coverRE[j, i], x[j]));
                //    }
                //    cplex.AddGe(eCoverLimit, 1);
                //    iCnstrNum++;
                //}
                //式7 交路运营数量约束
                INumExpr roueNumLimit = cplex.NumExpr();
                for (int i = 0; i < rNum; i++)
                {
                    roueNumLimit = cplex.Sum(roueNumLimit, x[i]);
                }
                cplex.AddLe(roueNumLimit, rMaxNum);
                iCnstrNum++;
                //式8  交路编组数量约束 
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            cplex.AddLe(cplex.Prod(y[i][j][k], mM[k]), mMaxR[i]);
                //            iCnstrNum++;
                //        }
                //    }
                //}
                for (int i = 0; i < rNum; i++)
                {
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            cplex.AddLe(cplex.Prod(y[i][j][k][0], mM[k]), mMaxR[i]);
                            cplex.AddLe(cplex.Prod(y[i][j][k][1], mM[k]), mMaxR[i]);
                            iCnstrNum++;
                        }
                    }
                }
                //iCnstrNum++;
                //式9 断面运力约束
                for (int i = 0; i < eNum; i++)
                {
                    INumExpr eUpCapLimit = cplex.NumExpr();
                    INumExpr eDownCapLimit = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        if (coverRE[j, i] == 1)
                        {
                            for (int k = 0; k < mNum; k++)
                            {
                                INumExpr mUpTrainCost = cplex.NumExpr();
                                INumExpr mDownTrainCost = cplex.NumExpr();
                                for (int ki = 0; ki < fNum; ki++)
                                {
                                    mUpTrainCost = cplex.Sum(mUpTrainCost, y[j][ki][k][0]);
                                    mDownTrainCost = cplex.Sum(mDownTrainCost, y[j][ki][k][1]);
                                }
                                mUpTrainCost = cplex.Prod(oM[k], mUpTrainCost);
                                eUpCapLimit = cplex.Sum(eUpCapLimit, mUpTrainCost);
                                mDownTrainCost = cplex.Prod(oM[k], mDownTrainCost);
                                eDownCapLimit = cplex.Sum(eDownCapLimit, mDownTrainCost);
                            }
                        }
                    }
                    eUpCapLimit = cplex.Prod(load, eUpCapLimit);
                    eDownCapLimit = cplex.Sum(load, eDownCapLimit);
                    cplex.AddGe(eUpCapLimit, pMaxE[i, 0]);
                    cplex.AddGe(eDownCapLimit, pMaxE[i, 1]);
                    iCnstrNum++;
                }
                //式10 线路通过能力约束
                for (int i = 0; i < eNum; i++)
                {
                    INumExpr eUpLineCapLimit = cplex.NumExpr();
                    INumExpr eDownLineCapLimit = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        if (coverRE[j, i] == 1)
                        {
                            for (int k = 0; k < fNum; k++)
                            {
                                for (int ki = 0; ki < mNum; ki++)
                                {
                                    eUpLineCapLimit = cplex.Sum(eUpLineCapLimit, y[j][k][ki][0]);
                                    eDownLineCapLimit = cplex.Sum(eDownLineCapLimit, y[j][k][ki][1]);
                                }
                            }
                        }
                    }
                    cplex.AddLe(eUpLineCapLimit, ceMaxE[i]);
                    cplex.AddGe(eUpLineCapLimit, ceMinE[i]);
                    iCnstrNum++;
                    cplex.AddGe(eDownLineCapLimit, ceMinE[i]);
                    cplex.AddLe(eDownLineCapLimit, ceMaxE[i]);
                    iCnstrNum++;
                }
                //式12 运用车数量约束
                //for (int i = 0; i < mNum; i++)
                //{
                //    INumExpr vehNumLimit = cplex.Diff(cplex.Prod(2, yM[i]), turnM[i]);
                //    cplex.AddLe(vehNumLimit, nM[i]);
                //    iCnstrNum++;
                //}
                //式15 接续唯一性约束
                //for (int i = 0; i < fNum; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr turnLimit = cplex.NumExpr();
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnLimit = cplex.Sum(turnLimit, turn[k][i][ki][j][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddLe(turnLimit, 1);
                //        iCnstrNum++;
                //    }
                //}
                //式16 接续唯一性约束
                //for (int i = 0; i < fNum; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr connLimit = cplex.NumExpr();
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        connLimit = cplex.Sum(connLimit, turn[k][kk][ki][j][kj][i]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddLe(connLimit, 1);
                //        iCnstrNum++;
                //    }
                //}
                //式17 折返关系之间的约束
                //for (int i = 0; i < fNum - 1; i++)
                //{
                //    for (int j = 0; j < dNum; j++)
                //    {
                //        INumExpr turnExpr = cplex.NumExpr();//折返关系之间的约束
                //        INumExpr behTurnExpr = cplex.NumExpr();//折返关系之间的约束
                //        for (int k = 0; k < rNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                int turnRouteNum = rTurnRR1[k].Count;
                //                for (int kj = 0; kj < turnRouteNum; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        turnExpr = cplex.Sum(turnExpr, turn[k][i][ki][j][kj][kk]);
                //                        behTurnExpr = cplex.Sum(behTurnExpr, turn[k][i + 1][ki][j][kj][kk]);
                //                    }
                //                }
                //            }
                //        }
                //        cplex.AddGe(turnExpr, behTurnExpr);
                //        iCnstrNum++;
                //    }
                //}
                //式18 式19  式22 式23 折返关系之间的约束
                //int iM1 = int.MaxValue;
                //int iM2 = int.MaxValue;
                //INumExpr[][][][] depTimeRFMD = new INumExpr[rNum][][][];
                //INumExpr[][][][] arrTimeRFMD = new INumExpr[rNum][][][];
                //for (int i = 0; i < rNum; i++)
                //{
                //    depTimeRFMD[i] = new INumExpr[fNum][][];
                //    arrTimeRFMD[i] = new INumExpr[fNum][][];
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        depTimeRFMD[i][j] = new INumExpr[mNum][];
                //        arrTimeRFMD[i][j] = new INumExpr[mNum][];
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            depTimeRFMD[i][j][k] = new INumExpr[dNum];
                //            arrTimeRFMD[i][j][k] = new INumExpr[dNum];
                //            INumExpr depTime = cplex.NumExpr();//列车i 运行方向为d 的出发时间表达式
                //            INumExpr arrTime = cplex.NumExpr();//列车i 运行方向为d 的出发时间表达式
                //            if (bIsDownDir)//如果下行为主要运营方向
                //            {
                //                depTimeRFMD[i][j][k][1] = cplex.Sum(cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //                depTimeRFMD[i][j][k][0] = cplex.Sum(z, cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //            }
                //            else//如果上行为主要运营方向
                //            {
                //                depTimeRFMD[i][j][k][0] = cplex.Sum(cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //                depTimeRFMD[i][j][k][1] = cplex.Sum(z, cplex.Prod((j - 1), h), cplex.Prod(iM2, cplex.Diff(1, y[i][j][k])));
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < rNum; i++)//根据基准站索引更新列车发车时间 与到达时间
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            int iDownStartStaIndex = rStaIndexListR2[i][0];
                //            int iDownEndStaIndex = rStaIndexListR2[i][1];
                //            depTimeRFMD[i][j][k][1] = cplex.Sum(depTimeRFMD[i][j][k][1], sRunS1S1D[iDownSrdStaIndex, iDownStartStaIndex, 1]);
                //            depTimeRFMD[i][j][k][0] = cplex.Sum(depTimeRFMD[i][j][k][0], sRunS1S1D[iUpSrdStaIndex, iDownEndStaIndex, 0]);
                //            arrTimeRFMD[i][j][k][1] = cplex.Sum(depTimeRFMD[i][j][k][1], rRunRD[i, 1]);
                //            arrTimeRFMD[i][j][k][0] = cplex.Sum(depTimeRFMD[i][j][k][0], rRunRD[i, 0]);
                //        }
                //    }
                //}
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int iAlterTurnRouteNum = rTurnRR1[i].Count;
                //                for (int kj = 0; kj < iAlterTurnRouteNum; kj++)
                //                {
                //                    int iAlterRouteIndex = rTurnRR1[i][kj];
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        cplex.AddGe(cplex.Sum(cplex.Diff(depTimeRFMD[iAlterRouteIndex][kk][k][1 - ki], arrTimeRFMD[i][j][k][ki]), cplex.Prod(iM1, cplex.Diff(1, turn[i][j][k][ki][kj][kk]))), rTurnRD[i, ki]);
                //                        iCnstrNum++;
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}
                //式20 变量x与y之间的约束
                for (int i = 0; i < rNum; i++)
                {
                    INumExpr yxLimit_Up = cplex.NumExpr();
                    INumExpr yxLimit_Down = cplex.NumExpr();
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            yxLimit_Up = cplex.Sum(yxLimit_Up, y[i][j][k][0]);
                            yxLimit_Down = cplex.Sum(yxLimit_Down, y[i][j][k][1]);
                        }
                    }
                    cplex.AddLe(yxLimit_Up, cplex.Prod(fNum, x[i]));
                    cplex.AddLe(yxLimit_Down, cplex.Prod(fNum, x[i]));
                    iCnstrNum++;
                }
                //新增约束 所有列车开行交路不能超过1
                for (int i = 0; i < fNum; i++)
                {
                    INumExpr trainNumLimit_Down = cplex.NumExpr();
                    INumExpr trainNumLimit_Up = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            trainNumLimit_Down = cplex.Sum(trainNumLimit_Down, y[j][i][k][1]);
                            trainNumLimit_Up = cplex.Sum(trainNumLimit_Up, y[j][i][k][0]);
                        }
                    }
                    cplex.AddLe(trainNumLimit_Down, 1);
                    cplex.AddLe(trainNumLimit_Up, 1);
                    iCnstrNum++;
                }
                //式21 变量y之间的约束
                for (int i = 0; i < fNum - 1; i++)
                {
                    INumExpr trainNum_Down = cplex.NumExpr();
                    INumExpr behTrainNum_Down = cplex.NumExpr();
                    INumExpr trainNum_Up = cplex.NumExpr();
                    INumExpr behTrainNum_Up = cplex.NumExpr();
                    for (int j = 0; j < rNum; j++)
                    {
                        for (int k = 0; k < mNum; k++)
                        {
                            trainNum_Down = cplex.Sum(trainNum_Down, y[j][i][k][1]);
                            behTrainNum_Down = cplex.Sum(behTrainNum_Down, y[j][i + 1][k][1]);
                            trainNum_Up = cplex.Sum(trainNum_Up, y[j][i][k][0]);
                            behTrainNum_Up = cplex.Sum(behTrainNum_Up, y[j][i + 1][k][0]);
                        }
                    }
                    cplex.AddGe(trainNum_Down, behTrainNum_Down);
                    cplex.AddGe(trainNum_Up, behTrainNum_Up);
                }
                //线性化的约束   式29-33
                //int iM3 = int.MaxValue;
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < sNum; ki++)
                //            {
                //                cplex.AddLe(liner1[i][j][k][ki], cplex.Prod(iM3 * coverRS[i, ki], y[i][j][k]));
                //                iCnstrNum++;
                //                cplex.AddLe(liner1[i][j][k][ki], wS[ki]);
                //                iCnstrNum++;
                //                cplex.AddGe(liner1[i][j][k][ki], cplex.Diff(wS[ki], cplex.Prod(iM3, cplex.Diff(1, cplex.Prod(coverRS[i, ki], y[i][j][k])))));
                //                iCnstrNum++;
                //            }
                //        }
                //    }
                //}
                //for (int i = 0; i < sNum; i++)
                //{
                //    INumExpr waitTimeLimit = cplex.NumExpr();
                //    for (int j = 0; j < rNum; j++)
                //    {
                //        for (int k = 0; k < fNum; k++)
                //        {
                //            for (int ki = 0; ki < mNum; ki++)
                //            {
                //                waitTimeLimit = cplex.Sum(waitTimeLimit, liner1[j][k][ki][i]);
                //            }
                //        }
                //    }
                //    int iPasNum = 0;
                //    for (int j = 0; j < sNum; j++)
                //    {
                //        iPasNum += pSS[i, j];
                //    }
                //    cplex.AddEq(waitTimeLimit, iPasNum * tNum);
                //    iCnstrNum++;
                //}
                //线性化的约束   式34-38
                //int iM4 = int.MaxValue;
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            cplex.AddLe(liner2[i][j][k], cplex.Prod(iM4, y[i][j][k]));
                //            iCnstrNum++;
                //            cplex.AddLe(liner2[i][j][k], h);
                //            iCnstrNum++;
                //            cplex.AddGe(liner2[i][j][k], cplex.Diff(h, cplex.Prod(iM4, cplex.Diff(1, y[i][j][k]))));
                //            iCnstrNum++;
                //        }
                //    }
                //}
                //INumExpr headwayLimit = cplex.NumExpr();//间隔等式约束
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            headwayLimit = cplex.Sum(headwayLimit, liner2[i][j][k]);
                //        }
                //    }
                //}
                //cplex.AddEq(headwayLimit, tNum);
                //iCnstrNum++;
                //新增折返约束 要保持到达列车与出发列车的折返站是一致的  看要不要补充到论文里
                //for (int i = 0; i < rNum; i++)
                //{
                //    for (int j = 0; j < fNum; j++)
                //    {
                //        for (int k = 0; k < mNum; k++)
                //        {
                //            for (int ki = 0; ki < dNum; ki++)
                //            {
                //                int iTurnRCount = rTurnRR1[i].Count;
                //                for (int kj = 0; kj < iTurnRCount; kj++)
                //                {
                //                    for (int kk = 0; kk < fNum; kk++)
                //                    {
                //                        cplex.AddEq(cplex.Prod(turn[i][j][k][ki][kj][kk], rStaIndexListR2[i][ki]), cplex.Prod(turn[i][j][k][ki][kj][kk], rStaIndexListR2[kj][1 - ki]));
                //                        iCnstrNum++;
                //                    }
                //                }
                //            }
                //        }
                //    }
                //}

                //新增关于目标函数的约束
                cplex.AddEq(z, z1);
                cplex.AddGe(z, Z1Cnstr);
                #endregion

                if (cplex.Solve())
                {
                    DownTrainRouteList = new List<DiagramRoute>();
                    UpTrainRouteList = new List<DiagramRoute>();

                    if (cplex.GetStatus().Equals(Cplex.Status.Infeasible))
                    {
                        Debug.WriteLine("No Solution");
                        return;
                    }

                    // Print results
                    Debug.WriteLine("Solution status = " + cplex.GetStatus());
                    Debug.WriteLine("Cost:" + cplex.ObjValue);
                    Debug.WriteLine("Z:" + cplex.GetValue(z));
                    Z1 = cplex.ObjValue;
                    //Debug.WriteLine("交路选择:");
                    //for (int i = 0; i < rNum; i++)
                    //{
                    //    double iRouteSelect = cplex.GetValue(x[i]);
                    //    if (iRouteSelect == 1)
                    //    {
                    //        string routeInfo = AlterRouteList[i].RouteName;
                    //        Debug.WriteLine("(" + i + ") " + routeInfo);
                    //    }
                    //}

                    Debug.WriteLine("上行列车开行:");
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int i = 0; i < rNum; i++)
                        {
                            for (int k = 0; k < mNum; k++)
                            {
                                double trainSelect_Up = cplex.GetValue(y[i][j][k][0]);
                                if (trainSelect_Up != 0)
                                {
                                    string routeInfo = AlterRouteList[i].RouteName;
                                    UpTrainRouteList.Add(AlterRouteList[i].ConverseRoute);
                                    Debug.WriteLine(routeInfo + "  上行" + "  第" + j + "列  编组" + mM[k]);
                                }
                            }
                        }
                    }

                    Debug.WriteLine("下行列车开行:");
                    for (int j = 0; j < fNum; j++)
                    {
                        for (int i = 0; i < rNum; i++)
                        {
                            for (int k = 0; k < mNum; k++)
                            {
                                double trainSelect_Down = cplex.GetValue(y[i][j][k][1]);
                                if (trainSelect_Down != 0)
                                {
                                    string routeInfo = AlterRouteList[i].RouteName;
                                    DownTrainRouteList.Add(AlterRouteList[i]);
                                    Debug.WriteLine(routeInfo + "  下行" + "  第" + j + "列  编组" + mM[k]);
                                }
                            }
                        }
                    }
                    //目标函数费用以及运力运量匹配情况
                    //double totalCost = 0;
                    //for (int i = 0; i < mNum; i++)
                    //{
                    //    double mZ12 = 0;
                    //    for (int j = 0; j < rNum; j++)
                    //    {
                    //        double rTrainCost = 0;
                    //        for (int k = 0; k < fNum; k++)
                    //        {
                    //            rTrainCost += cplex.GetValue(y[j][k][i][0]);
                    //            rTrainCost += cplex.GetValue(y[j][k][i][1]);
                    //        }
                    //        rTrainCost = rMileR[j] * rTrainCost;
                    //        mZ12 += rTrainCost;
                    //    }
                    //    mZ12 = mZ12 * c2M[i];
                    //    totalCost += mZ12;
                    //}

                    //Debug.WriteLine("目标函数计算值:" + totalCost * weight);


                    //Debug.WriteLine("上行运力运量匹配：");
                    //for (int i = 0; i < eNum; i++)
                    //{
                    //    double eTrainCap = 0;
                    //    for (int j = 0; j < rNum; j++)
                    //    {
                    //        if (coverRE[j, i] == 1)
                    //        {
                    //            for (int k = 0; k < fNum; k++)
                    //            {
                    //                for (int ki = 0; ki < mNum; ki++)
                    //                {
                    //                    double trainSelect_Up = cplex.GetValue(y[j][k][ki][0]);
                    //                    eTrainCap += trainSelect_Up * oM[ki];
                    //                }
                    //            }
                    //        }
                    //    }
                    //    string strInfo = CurLine.SectionList[i].strUpSectionName + "  " + pMaxE[i, 0] + "  " + eTrainCap;
                    //    Debug.WriteLine(strInfo);
                    //}

                    //Debug.WriteLine("下行运力运量匹配：");
                    //for (int i = 0; i < eNum; i++)
                    //{
                    //    double eTrainCap = 0;
                    //    for (int j = 0; j < rNum; j++)
                    //    {
                    //        if (coverRE[j, i] == 1)
                    //        {
                    //            for (int k = 0; k < fNum; k++)
                    //            {
                    //                for (int ki = 0; ki < mNum; ki++)
                    //                {
                    //                    double trainSelect_Down = cplex.GetValue(y[j][k][ki][1]);
                    //                    eTrainCap += trainSelect_Down * oM[ki];
                    //                }
                    //            }
                    //        }
                    //    }
                    //    string strInfo = CurLine.SectionList[i].strDownSectionName + "  " + pMaxE[i, 1] + "  " + eTrainCap;
                    //    Debug.WriteLine(strInfo);
                    //}

                    //Debug.WriteLine("偏移量:" + cplex.GetValue(z));

                    //Debug.WriteLine("接续情况:");
                    //int iTurnNum = 0;
                    //for (int i = 0; i < rNum; i++)
                    //{
                    //    for (int j = 0; j < fNum; j++)
                    //    {
                    //        for (int k = 0; k < mNum; k++)
                    //        {
                    //            for (int ki = 0; ki < dNum; ki++)
                    //            {
                    //                for (int kj = 0; kj < rTurnRR1[i].Count; kj++)
                    //                {
                    //                    double[] turnInfo = cplex.GetValues(turn[i][j][k][ki][kj]);
                    //                    for (int kk = 0; kk < fNum; kk++)
                    //                    {
                    //                        if (turnInfo[kk] == 1)
                    //                        {
                    //                            iTurnNum++;
                    //                            string dir = "下行";
                    //                            string reDir = "上行";
                    //                            if (ki == 0)
                    //                            {
                    //                                dir = "上行";
                    //                                reDir = "下行";
                    //                            }
                    //                            string strTurnInfo = AlterRouteList[i].RouteName + "  " + j + "  " + mM[k] + "  " + dir + "——";
                    //                            strTurnInfo += AlterRouteList[rTurnRR1[i][kj]].RouteName + "  " + kk + "  " + mM[k] + "  " + reDir;
                    //                            Debug.WriteLine("(" + iTurnNum + ") " + strTurnInfo);
                    //                        }
                    //                    }
                    //                }
                    //            }
                    //        }
                    //    }
                    //}

                    //Debug.WriteLine("车站乘客候车时间:");
                    //double[] staWaitTime = cplex.GetValues(wS);
                    //for (int i = 0; i < sNum; i++)
                    //{
                    //    string strStaWaitTime = CurLine.StationList[i].strStationName + "  " + staWaitTime[i];
                    //    Debug.WriteLine(strStaWaitTime);
                    //}

                    //Debug.WriteLine("行车间隔:" + cplex.GetValue(h));

                }

                cplex.End();
            }
            catch (ILOG.Concert.Exception exc)
            {
                Debug.WriteLine("Concert exception '" + exc + "' caught");
            }
        }
    }

    public class PasWaitTimeCal
    {
        public CapRsceAllocPro CurCapRsceAllocPro { get; set; }
        public TimeOperationInfo CurTimeOper { get; set; }
        public TimeOperationInfo BehTimeOperInfo { get; set; }
        public TrainDiagramStructure CurrentTrainDiagram { get; set; }
        public double dWeight { get; set; }//权重
        public BasicDataOfLine BelongedLine { get; set; }
        List<DiagramRoute> RouteList { get; set; }
        List<RouteStation> RetyStationList { get; set; }
        int iMinItvl { get; set; }
        int[,] routeCoverArray;
        double c3 = 25.0 / 3600;
        #region 计算单一交路 最小行车间隔计算最小等待时间
        public double CalMinWaitTimeCost(List<AFCPassengerDataStructure> ODPasDataList) //基于最小等待时间计算乘客等待时间成本
        {
            double dPasWaitTime = 0;
            InitialParamter();
            CurrentTrainDiagram.TrainDiagramTimeTableList.Clear();
            GnrtTrainDiagram(CurTimeOper);
            CurrentTrainDiagram.SetDiagramPassbyStation();
            //InputTrainDiagramStationPass();
            List<AFCPassengerDataStructure> odPasDataList = ODPasDataList;
            int iPasNum = 0;
            for (int i = 0; i < odPasDataList.Count; i++)
            {
                AFCPassengerDataStructure odPas = odPasDataList[i];
                odPas.dtEnterTime = odPas.SetStrtimeToDatetime(DateTime.Now.ToString("yyyyMMdd"), odPas.InStationTime);
                TrainDiagramStationStructure oriTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.OriStationName);
                TrainDiagramStationStructure desTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.DesStationName);
                if (oriTrainDiagramSta != null && desTrainDiagramSta != null)
                {
                    int oriStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.OriStationName);
                    int desStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.DesStationName);
                    bool bIsDown = true;
                    if (oriStaIndex > desStaIndex) bIsDown = false;
                    List<StationTrainLineStructure> searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Down;
                    if (!bIsDown) searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Up;
                    DateTime staRightTime = searchStaTrainLine[searchStaTrainLine.Count - 1].StationTime.DepDateTime;
                    //DateTime staLeftTime = searchStaTrainLine[0].StationTime.ArrDateTime;
                    if (odPas.dtEnterTime < staRightTime)
                    {
                        StationTrainLineStructure selectTrain = searchStaTrainLine.Find(item => item.StationTime.DepDateTime > odPas.dtEnterTime);
                        dPasWaitTime += (selectTrain.StationTime.DepDateTime - odPas.dtEnterTime).TotalSeconds;
                        iPasNum++;
                    }
                    else
                    {
                        continue;
                    }
                }
                else
                {

                }
            }
            dPasWaitTime = dPasWaitTime * c3 * dWeight;
            return dPasWaitTime;
        }
        public double CalMinOperCostWaitTimeCost()//计算最小运营成本对应的乘客等待时间成本
        {
            double dPasWaitTime = 0;

            return dPasWaitTime;
        }
        private void InitialParamter()
        {
            BelongedLine = CurCapRsceAllocPro.BelongedLine;
            CurTimeOper = new TimeOperationInfo();
            CurTimeOper.BehTimeOper = BehTimeOperInfo;
            iMinItvl = 150;
            CurTimeOper.dtStartTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "05:30:00");
            CurTimeOper.dtLastTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "12:00:00");
            CurTimeOper.TimeSecRunScale = DataHandler.GetSecRunScaleData("3号线工作日平峰运行标尺_001");
            CurTimeOper.TimeStaStopScale = DataHandler.GetStaStopScaleData("3号线工作日平峰停站标尺_001");
            List<string> strRouteInfoList = new List<string>();
            strRouteInfoList.Add("鱼洞-江北机场T2航站楼");
            RouteList = new List<DiagramRoute>();
            for (int j = 0; j < strRouteInfoList.Count; j++)//不管是否为多交路总会有一个空的数组
            {
                string strRouteInfo = strRouteInfoList[j];
                if (strRouteInfo == string.Empty || strRouteInfo == null) continue;
                if (strRouteInfo.Contains("(独立运营)"))
                {
                    strRouteInfo = strRouteInfo.Replace("(独立运营)", "");
                    string[] stSingleRoutexInfo = strRouteInfo.Split('-');
                    string routeStartName = stSingleRoutexInfo[0];
                    string routeLastName = stSingleRoutexInfo[1];
                    CreateDiagramRoute(BelongedLine.StationList, routeStartName, routeLastName);
                }
                else
                {
                    string[] stSingleRoutexInfo = strRouteInfo.Split('-');
                    string routeStartName = stSingleRoutexInfo[0];
                    string routeLastName = stSingleRoutexInfo[1];
                    CreateDiagramRoute(BelongedLine.StationList, routeStartName, routeLastName);
                }
            }
            RetyStationList = new List<RouteStation>();
            CurTimeOper.RouteList = RouteList;
            for (int i = 0; i < RouteList.Count; i++)
            {
                DiagramRoute route = RouteList[i];
                RouteStation startSta = route.RouteStationList[0];
                RouteStation lastSta = route.RouteStationList[route.RouteStationList.Count - 1];
                if (!RetyStationList.Exists(item => item.StationName == startSta.StationName))
                {
                    RetyStationList.Add(startSta);
                }
                if (!RetyStationList.Exists(item => item.StationName == lastSta.StationName))
                {
                    RetyStationList.Add(lastSta);
                }
            }
            RetyStationList.Sort(delegate (RouteStation rSta1, RouteStation rSta2)
            {
                return rSta1.StaIndex.CompareTo(rSta2.StaIndex);
            });
            routeCoverArray = new int[RouteList.Count, RetyStationList.Count];
            for (int i = 0; i < RouteList.Count; i++)
            {
                for (int j = 0; j < RetyStationList.Count; j++)
                {
                    routeCoverArray[i, j] = 0;
                    if (RouteList[i].RouteStationList.Exists(item => item.StationName == RetyStationList[j].StationName))
                    {
                        routeCoverArray[i, j] = 1;
                    }
                }
            }
            for (int i = 0; i < RouteList.Count; i++)
            {
                DiagramRoute route = RouteList[i];
                route.SetRouteRunKilo(route.BelongLine);
            }
        }
        private void CreateDiagramRoute(List<BasicDataOfStation> staList, string startSta, string lastSta)//创建交路
        {
            //下行
            DiagramRoute downRoute = new DiagramRoute();
            downRoute.BelongLine = BelongedLine;
            downRoute.StartStationName = startSta;
            downRoute.LastStationName = lastSta;
            downRoute.RouteName = startSta + "-" + lastSta;
            downRoute.bIsBasicRoute = false;
            downRoute.bIsDownDir = true;
            bool bIsStart = false;
            for (int i = 0; i < staList.Count; i++)
            {
                BasicDataOfStation sta = staList[i];
                if (sta.strStationName == startSta)
                {
                    bIsStart = true;
                    RouteStation rStation = new RouteStation();
                    rStation.iMaxTrainMation = sta.iMaxTrainMation;
                    rStation.StaIndex = sta.l_iStationNo;
                    rStation.LineName = sta.strLineName;
                    rStation.StationName = sta.strStationName;
                    rStation.strTurnType = sta.strTurnType;
                    rStation.strTurnCapacity = sta.strTurnCapacity;
                    rStation.StationType = sta.iStationType;
                    rStation.iRetyCondition = sta.iRetyCondition;
                    rStation.iTurnTrainNumCnstr = sta.iRetyTrainCnstr;
                    rStation.iTurnType = sta.iTurnType;
                    rStation.iTurnCnstrCap = sta.iStationRstcap;
                    if (sta.iTurnType != 3)
                    {
                        rStation.iTurnCapacity = Convert.ToInt32(sta.strTurnCapacity);
                    }
                    downRoute.RouteStationList.Add(rStation);
                }
                else if (bIsStart)
                {
                    RouteStation rStation = new RouteStation();
                    rStation.StaIndex = sta.l_iStationNo;
                    rStation.iMaxTrainMation = sta.iMaxTrainMation;
                    rStation.LineName = sta.strLineName;
                    rStation.StationName = sta.strStationName;
                    rStation.strTurnType = sta.strTurnType;
                    rStation.strTurnCapacity = sta.strTurnCapacity;
                    rStation.StationType = sta.iStationType;
                    rStation.iRetyCondition = sta.iRetyCondition;
                    rStation.iTurnTrainNumCnstr = sta.iRetyTrainCnstr;
                    rStation.iTurnCnstrCap = sta.iStationRstcap;
                    downRoute.RouteStationList.Add(rStation);
                    rStation.iTurnType = sta.iTurnType;
                    if (sta.iTurnType != 3)
                    {
                        rStation.iTurnCapacity = Convert.ToInt32(sta.strTurnCapacity);
                    }
                    if (sta.strStationName == lastSta)
                    {
                        break;
                    }
                }
            }
            if (downRoute.RouteStationList.Count < 3) return;
            RouteList.Add(downRoute);
            //上行
            DiagramRoute upRoute = new DiagramRoute();
            upRoute.BelongLine = BelongedLine;
            upRoute.StartStationName = lastSta;
            upRoute.LastStationName = startSta;
            upRoute.RouteName = lastSta + "-" + startSta;
            upRoute.bIsBasicRoute = false;
            upRoute.bIsDownDir = false;
            bIsStart = false;
            for (int i = staList.Count - 1; i >= 0; i--)
            {
                BasicDataOfStation sta = staList[i];
                if (sta.strStationName == lastSta)
                {
                    bIsStart = true;
                    RouteStation rStation = new RouteStation();
                    rStation.StaIndex = sta.l_iStationNo;
                    rStation.LineName = sta.strLineName;
                    rStation.StationName = sta.strStationName;
                    rStation.strTurnType = sta.strTurnType;
                    rStation.strTurnCapacity = sta.strTurnCapacity;
                    rStation.StationType = sta.iStationType;
                    rStation.iRetyCondition = sta.iRetyCondition;
                    rStation.iMaxTrainMation = sta.iMaxTrainMation;
                    rStation.iTurnCnstrCap = sta.iStationRstcap;
                    rStation.iTurnTrainNumCnstr = sta.iRetyTrainCnstr;
                    rStation.iTurnType = sta.iTurnType;
                    if (sta.iTurnType != 3)
                    {
                        rStation.iTurnCapacity = Convert.ToInt32(sta.strTurnCapacity);
                    }
                    upRoute.RouteStationList.Add(rStation);
                }
                else if (bIsStart)
                {
                    RouteStation rStation = new RouteStation();
                    rStation.StaIndex = sta.l_iStationNo;
                    rStation.LineName = sta.strLineName;
                    rStation.StationName = sta.strStationName;
                    rStation.strTurnType = sta.strTurnType;
                    rStation.strTurnCapacity = sta.strTurnCapacity;
                    rStation.StationType = sta.iStationType;
                    upRoute.RouteStationList.Add(rStation);
                    rStation.iRetyCondition = sta.iRetyCondition;
                    rStation.iMaxTrainMation = sta.iMaxTrainMation;
                    rStation.iTurnCnstrCap = sta.iStationRstcap;
                    rStation.iTurnTrainNumCnstr = sta.iRetyTrainCnstr;
                    rStation.iTurnType = sta.iTurnType;
                    if (sta.iTurnType != 3)
                    {
                        rStation.iTurnCapacity = Convert.ToInt32(sta.strTurnCapacity);
                    }
                    if (sta.strStationName == startSta)
                    {
                        break;
                    }
                }
            }
            //UpInitialRouteList.Add(upRoute);
            downRoute.ConverseRoute = upRoute;
            upRoute.ConverseRoute = downRoute;
        }
        private void GnrtTrainDiagram(TimeOperationInfo timeOperInfo)
        {
            //bIsLeft 是否是从右向左进行列车运行线生成
            bool bIsLeft = true;
            List<TrainDiagramTimeTableStructure> gnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            SectionRunScale secRunScale = timeOperInfo.TimeSecRunScale;
            StationStopScale staStopScale = timeOperInfo.TimeStaStopScale;
            List<DiagramRoute> revsDiagramRouteList = new List<DiagramRoute>();
            for (int i = 0; i < timeOperInfo.RouteList.Count; i++)
            {
                DiagramRoute revsRoute = timeOperInfo.RouteList[i].ConverseRoute;
                revsDiagramRouteList.Add(revsRoute);
            }
            TrainDiagramTimeTableStructure srdDownTrain = BehTimeOperInfo.DownTrainList[0];
            gnrtTrainList.Add(srdDownTrain);
            timeOperInfo.iMinTrainInterval = 150;
            DateTime dtStartTime = srdDownTrain.dtVirtStartTime;
            double dRunInterval = -1 * iMinItvl;
            //dRunInterval = CalTrainItvlBySecPas(srdDownTrain, timeOperInfo, bIsLeft);
            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            DateTime dtLastTime = timeOperInfo.dtStartTime;
            int iTrainIndex = 0;
            List<DiagramRoute> timeCalRouteCalList = timeOperInfo.RouteList;
            if (!timeOperInfo.bIsDownDir) timeCalRouteCalList = revsDiagramRouteList;
            List<DateTime> trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            while (dtStartTime > dtLastTime || iTrainIndex % timeOperInfo.iTotalRouteNum != 0)
            {
                int iRouteIndex = iTrainIndex % timeOperInfo.iTotalRouteNum;
                if (bIsLeft) iRouteIndex = timeOperInfo.iTotalRouteNum - 1 - iRouteIndex;
                DiagramRoute useRoute = timeOperInfo.RouteList[iRouteIndex];
                if (!timeOperInfo.bIsDownDir) useRoute = useRoute.ConverseRoute;
                DateTime dtTrainStartTime = trainStartTimeList[iRouteIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, timeOperInfo, dtTrainStartTime, dtStartTime);
                gnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= timeOperInfo.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(timeOperInfo, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int i = 0; i < trainStartTimeList.Count; i++)
                        {
                            trainStartTimeList[i] = trainStartTimeList[i].AddSeconds(iOffset);
                        }
                    }
                }
                //dRunInterval = CalTrainItvlBySecPas(train, timeOperInfo, bIsLeft);
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int i = 0; i < trainStartTimeList.Count; i++)
                {
                    trainStartTimeList[i] = trainStartTimeList[i].AddSeconds(dRunInterval);
                }
            }
            //绘制非主要列车运营方向的列车运行线
            List<TrainDiagramTimeTableStructure> rvseGnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            TrainDiagramTimeTableStructure srdUpTrain = timeOperInfo.BehTimeOper.UpTrainList[0];
            timeOperInfo.iMinTrainInterval = timeOperInfo.BehTimeOper.iMinTrainInterval;
            rvseGnrtTrainList.Add(srdUpTrain);
            dtStartTime = srdUpTrain.dtVirtStartTime;
            //dRunInterval = CalTrainItvlBySecPas(srdUpTrain, timeOperInfo, bIsLeft);
            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            timeCalRouteCalList = timeOperInfo.RouteList;
            if (timeOperInfo.bIsDownDir) timeCalRouteCalList = revsDiagramRouteList;
            trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            iTrainIndex = 0;
            while (dtStartTime > dtLastTime || iTrainIndex % timeOperInfo.iTotalRouteNum != 0)
            {
                int iRouteIndex = iTrainIndex % timeOperInfo.iTotalRouteNum;
                if (bIsLeft) iRouteIndex = timeOperInfo.iTotalRouteNum - 1 - iRouteIndex;
                DiagramRoute useRoute = timeOperInfo.RouteList[iRouteIndex];
                if (timeOperInfo.bIsDownDir) useRoute = useRoute.ConverseRoute;
                DateTime dtTrainStartTime = trainStartTimeList[iRouteIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, timeOperInfo, dtTrainStartTime, dtStartTime);
                rvseGnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= timeOperInfo.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(timeOperInfo, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int i = 0; i < trainStartTimeList.Count; i++)
                        {
                            trainStartTimeList[i] = trainStartTimeList[i].AddSeconds(iOffset);
                        }
                    }
                }
                //dRunInterval = CalTrainItvlBySecPas(train, timeOperInfo, bIsLeft);
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int i = 0; i < trainStartTimeList.Count; i++)
                {
                    trainStartTimeList[i] = trainStartTimeList[i].AddSeconds(dRunInterval);
                }
            }
            //将生成的列车运行线添加到分时集合中
            if (bIsLeft)
            {
                gnrtTrainList.Reverse();
                rvseGnrtTrainList.Reverse();
            }
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(gnrtTrainList);
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(rvseGnrtTrainList);
            if (timeOperInfo.bIsDownDir)
            {
                timeOperInfo.DownTrainList.AddRange(gnrtTrainList);
                timeOperInfo.UpTrainList.AddRange(rvseGnrtTrainList);
            }
            else
            {
                timeOperInfo.UpTrainList.AddRange(gnrtTrainList);
                timeOperInfo.DownTrainList.AddRange(rvseGnrtTrainList);
            }
            BuildRelationTrainListAndDiagramStation();
        }
        private List<DateTime> CalTrainStartTimeList(List<DiagramRoute> routeList, SectionRunScale secRunScale, StationStopScale staStopScale, DateTime dtStartTime)
        {
            List<DateTime> trainStartTimeList = new List<DateTime>();
            trainStartTimeList.Add(dtStartTime);
            DiagramRoute srdRoute = routeList[0];
            for (int i = 1; i < routeList.Count; i++)
            {
                DiagramRoute otherRoute = routeList[i];
                DateTime dtOtherStartTime = CalculateRouteTrainStartTime(dtStartTime, srdRoute, otherRoute, secRunScale, staStopScale);
                trainStartTimeList.Add(dtOtherStartTime);
            }
            return trainStartTimeList;
        }
        private TrainDiagramTimeTableStructure GenerateSingleTrainTimeTable(DiagramRoute trainRoute, TimeOperationInfo timeOperInfo, DateTime dtTrainStartTime, DateTime dtVirtStartTime)//生成单一列车运行线
        {
            //判断列车运行线是否与前边的列车运行线不满足最小行车间隔约束，如果不满足则不进行列车运行线的生成
            CurCapRsceAllocPro.BuildScaleAndRouteRelation(trainRoute, timeOperInfo.TimeSecRunScale, timeOperInfo.TimeStaStopScale);
            TrainDiagramTimeTableStructure train = new TrainDiagramTimeTableStructure();
            //train.BelongDiagram = CurrentTrainDiagram;
            //train.BelongDiagram = CurrentTrainDiagram;
            train.dtVirtStartTime = dtVirtStartTime;
            train.LineName = CurCapRsceAllocPro.LineName;
            train.IsDownTrain = trainRoute.bIsDownDir;
            double dStopTime = 0;
            double dRunTime = 0;//运行时间，包含累计的停站和区间运行时间
            int iStaNo = 0;
            for (int i = 0; i < trainRoute.RouteStationList.Count; i++)
            {
                RouteStation rStation = trainRoute.RouteStationList[i];
                StationTrainLineStructure trainDiagramLine = new StationTrainLineStructure();
                trainDiagramLine.StationName = rStation.StationName;
                trainDiagramLine.StationNo = iStaNo;
                trainDiagramLine.StaType = rStation.StationType;
                iStaNo++;
                trainDiagramLine.LineName = rStation.LineName;
                //确定停站时间
                dStopTime = 0;
                if (train.IsDownTrain)
                {
                    dStopTime = rStation.StaStopTime.DownStopTime;
                    if (i == trainRoute.RouteStationList.Count - 1)
                        dStopTime = rStation.StaStopTime.DownStopTime_T;
                    else if (i == 0)
                    {
                        dStopTime = rStation.StaStopTime.DownStopTime_S;
                    }
                }
                else
                {
                    dStopTime = rStation.StaStopTime.UpStopTime;
                    if (i == trainRoute.RouteStationList.Count - 1)
                    {
                        dStopTime = rStation.StaStopTime.UpStopTime_T;
                        //dStopTime = 0;
                    }

                    else if (i == 0)
                    {
                        dStopTime = rStation.StaStopTime.UpStopTime_S;
                        //dStopTime = 0;
                    }
                }
                //计算列车到达离开时间
                trainDiagramLine.StationTime.strArrTime = dtTrainStartTime.AddSeconds(dRunTime).ToString("HH:mm:ss");
                trainDiagramLine.StationTime.strDepTime = dtTrainStartTime.AddSeconds(dRunTime).AddSeconds(dStopTime).ToString("HH:mm:ss");
                //累加区间运行时间和停站时间
                if (i != trainRoute.RouteStationList.Count - 1)
                {
                    if (train.IsDownTrain)
                    {
                        dRunTime += rStation.SecRunTime.DownRunTime;
                        dRunTime += dStopTime;
                    }
                    else
                    {
                        dRunTime += rStation.SecRunTime.UpRunTime;
                        dRunTime += dStopTime;
                    }
                }
                trainDiagramLine.BelongedTimeTable = train;
                train.StationTrainLineList.Add(trainDiagramLine);
                //支线分岔点车站不管上下行都要添加两个车站列车运行线,做特殊处理
                //if (rStation.StationType == 2)
                //{
                //    if (trainRoute.bIsBasicRoute)//只针对大交路进行列车运行线的添加
                //    {
                //        StationTrainLineStructure trainBranchStaLine = new StationTrainLineStructure();//分岔车站的第二条线
                //        trainBranchStaLine.StationName = rStation.StationName;
                //        trainBranchStaLine.StationNo = iStaNo;
                //        iStaNo++;
                //        trainBranchStaLine.LineName = rStation.LineName;
                //        trainBranchStaLine.StationTime.strArrTime = trainDiagramLine.StationTime.strArrTime;
                //        trainBranchStaLine.StationTime.strDepTime = trainDiagramLine.StationTime.strDepTime;
                //        trainBranchStaLine.BelongedTimeTable = train;
                //        train.StationTrainLineList.Add(trainBranchStaLine);
                //    }
                //}
            }
            train.TrainRoute = trainRoute;
            train.BelongTimeOper = timeOperInfo;
            //train.TrainLineDrawStru.TrainBrush = TrainBrush;
            //train.InitialTrainAdjsutInfo();
            return train;
        }
        private DateTime CalculateRouteTrainStartTime(DateTime dtRouteTrainStartTime, DiagramRoute basicRoute
              , DiagramRoute calRoute, SectionRunScale secRunScale, StationStopScale staStopScale)//依据其它交路计算某路列车发车时间主要针对交路起始车站不重合的车站
        {
            //首先要找到大小交路最早开始有重叠的车站
            DateTime dtCalRTrainStartTime = DateTime.MinValue;
            bool isDownTrain = basicRoute.bIsDownDir;
            int iFindStartIndex = -1;//在小交路中找到的开始车站
            int iStaStartIndex = -1;//在大交路中找到的与小交路最早开始有重叠的车站
            double iReachStartStaTime = 0;//运行到与小交路最早重叠车站的时间
            double iSRStartRunTime = 0;
            bool isFind = false;
            for (int i = 0; i < calRoute.RouteStationList.Count; i++)
            {
                RouteStation rShortStartSta = calRoute.RouteStationList[i];
                for (int j = 0; j < basicRoute.RouteStationList.Count; j++)
                {
                    RouteStation rLSta = basicRoute.RouteStationList[j];
                    if (rShortStartSta.StationName == rLSta.StationName)
                    {
                        iStaStartIndex = j;
                        iFindStartIndex = i;
                        isFind = true;
                        break;
                    }
                }
                if (isFind)
                    break;
            }
            //根据大交路的始发站开始时间计算大交路运行到iStaStartIndex索引车站的车站出发时间
            CurCapRsceAllocPro.BuildScaleAndRouteRelation(basicRoute, secRunScale, staStopScale);
            for (int i = 0; i <= iStaStartIndex; i++)
            {
                RouteStation rSta = basicRoute.RouteStationList[i];
                if (isDownTrain)
                {
                    if (i != iStaStartIndex)//不需要加最开始重叠车站的停站时间
                    {
                        iReachStartStaTime += rSta.SecRunTime.DownRunTime;
                    }
                    if (i == 0)
                    {
                        iReachStartStaTime += rSta.StaStopTime.DownStopTime_S;
                    }
                    else if (i == basicRoute.RouteStationList.Count - 1)
                    {
                        iReachStartStaTime += rSta.StaStopTime.DownStopTime_T;
                    }
                    else
                    {
                        iReachStartStaTime += rSta.StaStopTime.DownStopTime;
                    }
                }
                else
                {
                    if (i != iStaStartIndex)
                    {
                        iReachStartStaTime += rSta.SecRunTime.UpRunTime;
                    }
                    if (i == 0)
                    {
                        iReachStartStaTime += rSta.StaStopTime.UpStopTime_S;
                    }
                    else if (i == basicRoute.RouteStationList.Count - 1)
                    {
                        iReachStartStaTime += rSta.StaStopTime.UpStopTime_T;
                    }
                    else
                    {
                        iReachStartStaTime += rSta.StaStopTime.UpStopTime;
                    }
                }
            }
            dtRouteTrainStartTime = dtRouteTrainStartTime.AddSeconds(iReachStartStaTime);
            //根据大小交路重叠位置反推小交路列车的始发时间
            CurCapRsceAllocPro.BuildScaleAndRouteRelation(calRoute, secRunScale, staStopScale);
            for (int i = iFindStartIndex; i >= 0; i--)
            {
                RouteStation rSta = calRoute.RouteStationList[i];
                if (isDownTrain)
                {
                    if (i != iFindStartIndex)//不需要加最开始重叠车站的停站时间
                    {
                        iSRStartRunTime += rSta.SecRunTime.DownRunTime;
                    }
                    if (i == 0)
                    {
                        iSRStartRunTime += rSta.StaStopTime.DownStopTime_S;
                    }
                    else if (i == calRoute.RouteStationList.Count - 1)
                    {
                        iSRStartRunTime += rSta.StaStopTime.DownStopTime_T;
                    }
                    else
                    {
                        iSRStartRunTime += rSta.StaStopTime.DownStopTime;
                    }
                }
                else
                {
                    if (i != iFindStartIndex)
                    {
                        iSRStartRunTime += rSta.SecRunTime.UpRunTime;
                    }
                    if (i == 0)
                    {
                        iSRStartRunTime += rSta.StaStopTime.UpStopTime_S;
                    }
                    else if (i == calRoute.RouteStationList.Count - 1)
                    {
                        iSRStartRunTime += rSta.StaStopTime.UpStopTime_T;
                    }
                    else
                    {
                        iSRStartRunTime += rSta.StaStopTime.UpStopTime;
                    }
                }
            }
            dtCalRTrainStartTime = dtRouteTrainStartTime.AddSeconds(-iSRStartRunTime);
            return dtCalRTrainStartTime;
        }
        private int FirPeriodGnrtTrainTimeAdjust(TimeOperationInfo timeOperInfo, TrainDiagramTimeTableStructure checkTrain, bool bIsLeft)//由于标尺不一致导致该时段第一个周期生成的列车运行线与相邻时段的边界列车运行线之间存在间隔冲突
        {
            //bIsLeft判断当前时段是否是左侧时段 如果为是则被比较的是右侧时段  
            //timeOperInfo 要进行列车生成的运营时段 cmpTimeOperInfo 要进行比较的列车运营时段
            int xoffset = 0;
            TimeOperationInfo cmpTimeOperInfo = timeOperInfo.ForeTimeOper;
            if (bIsLeft)
                cmpTimeOperInfo = timeOperInfo.BehTimeOper;
            if (cmpTimeOperInfo == null || cmpTimeOperInfo.DownTrainList.Count == 0 || cmpTimeOperInfo.UpTrainList.Count == 0) return xoffset;
            List<TrainDiagramTimeTableStructure> cmpTrainList = new List<TrainDiagramTimeTableStructure>();
            int iCheckTrainCount = cmpTimeOperInfo.iTotalRouteNum;//比一个周期的列车运行线直至checkTrain 所有车站时刻都被确认没有冲突后结束
            if (checkTrain.IsDownTrain)
            {
                if (bIsLeft)//向前寻找找前向列车的最后一列列车
                {

                    for (int i = 0; i < iCheckTrainCount; i++)
                    {
                        TrainDiagramTimeTableStructure cmpTrain = cmpTimeOperInfo.DownTrainList[i];
                        cmpTrainList.Add(cmpTrain);
                    }
                }
                else
                {

                    for (int i = cmpTimeOperInfo.DownTrainList.Count - 1; i >= cmpTimeOperInfo.DownTrainList.Count - iCheckTrainCount; i--)
                    {
                        TrainDiagramTimeTableStructure cmpTrain = cmpTimeOperInfo.DownTrainList[i];
                        cmpTrainList.Add(cmpTrain);
                    }

                }
            }
            else
            {
                if (bIsLeft)//向前寻找找前向列车的最后一列列车
                {
                    for (int i = 0; i < iCheckTrainCount; i++)
                    {
                        TrainDiagramTimeTableStructure cmpTrain = cmpTimeOperInfo.UpTrainList[i];
                        cmpTrainList.Add(cmpTrain);
                    }
                }
                else
                {
                    for (int i = cmpTimeOperInfo.UpTrainList.Count - 1; i >= cmpTimeOperInfo.UpTrainList.Count - iCheckTrainCount; i--)
                    {
                        TrainDiagramTimeTableStructure cmpTrain = cmpTimeOperInfo.UpTrainList[i];
                        cmpTrainList.Add(cmpTrain);
                    }
                }
            }
            List<int> staDifItvlList = new List<int>();
            for (int i = 0; i < checkTrain.StationTrainLineList.Count; i++)
            {
                StationTrainLineStructure stationTrainLine = checkTrain.StationTrainLineList[i];
                StationTrainLineStructure cmpStationTrainLine = null;
                for (int j = 0; j < cmpTrainList.Count; j++)
                {
                    TrainDiagramTimeTableStructure cmpTrain = cmpTrainList[j];
                    cmpStationTrainLine = cmpTrain.StationTrainLineList.Find(item => item.StationName == stationTrainLine.StationName);
                    if (cmpStationTrainLine != null) break;
                }
                int iArrDifItvl = Math.Abs(stationTrainLine.StationTime.iArriveTime - cmpStationTrainLine.StationTime.iArriveTime);
                int iDepDifItvl = Math.Abs(stationTrainLine.StationTime.iDepartTime - cmpStationTrainLine.StationTime.iDepartTime);
                staDifItvlList.Add(iArrDifItvl);
                staDifItvlList.Add(iDepDifItvl);
            }
            int iMinItvl = staDifItvlList.Min();
            if (iMinItvl < cmpTimeOperInfo.iMinTrainInterval)
            {
                xoffset = cmpTimeOperInfo.iMinTrainInterval - iMinItvl;
            }
            if (bIsLeft)
            {
                xoffset = xoffset * -1;
            }
            return xoffset;
        }
        private void TrainTimeAdjust(TrainDiagramTimeTableStructure adjsutTrian, int offset)
        {
            for (int i = 0; i < adjsutTrian.StationTrainLineList.Count; i++)
            {
                StationTrainLineStructure staTrainLine = adjsutTrian.StationTrainLineList[i];
                DateTime dtArrTime = staTrainLine.StationTime.ArrDateTime.AddSeconds(offset);
                DateTime dtDepTime = staTrainLine.StationTime.DepDateTime.AddSeconds(offset);
                staTrainLine.StationTime.strArrTime = dtArrTime.ToString("HH:mm:ss");
                staTrainLine.StationTime.strDepTime = dtDepTime.ToString("HH:mm:ss");
            }
        }
        private int CalTrainItvlBySecPas(TrainDiagramTimeTableStructure srdTrain, TimeOperationInfo timeOperInfo, bool bIsLeft)
        {
            //bIsLeft 控制列车是否在左侧
            List<DateTime> dtSecStartTimeList = new List<DateTime>();
            List<DateTime> dtRecordTimeList = new List<DateTime>();
            List<string> strSecNameList = new List<string>();
            List<int> iPasNumList = new List<int>();
            //bool bIsDown = srdTrain.IsDownTrain;
            int iBasicLength = 5 * 60;//最小基准粒度
            int iTimeLength = 0;//客流计算时长
            if (bIsLeft) iBasicLength = -iBasicLength;
            int itvl = 0;
            double dTrainNum = 0;
            int iMaxSecPas = 0;
            List<SectionLinkForKSP> searchSecPasList = BelongedLine.SectionLinkList;
            //if (bIsDown) searchSecPasList = CurrentLine.DownSectionLinkList;
            string strPasInfo = string.Empty;
            for (int i = 1; i < srdTrain.StationTrainLineList.Count; i++)
            {
                StationTrainLineStructure startSta = srdTrain.StationTrainLineList[i - 1];
                StationTrainLineStructure lastSta = srdTrain.StationTrainLineList[i];
                string strSecName = startSta.StationName + "-" + lastSta.StationName;
                strSecNameList.Add(strSecName);
                dtSecStartTimeList.Add(startSta.StationTime.ArrDateTime);
                iPasNumList.Add(0);
            }
            while (iTimeLength < BelongedLine.iLineMaxItvl)
            {
                for (int i = 0; i < dtSecStartTimeList.Count; i++)
                {
                    DateTime dtStartTime = dtSecStartTimeList[i];
                    dtSecStartTimeList[i] = dtStartTime.AddSeconds(iBasicLength);
                }

                for (int i = 0; i < strSecNameList.Count; i++)
                {
                    string strSecName = strSecNameList[i];
                    DateTime dtSecTime = dtSecStartTimeList[i];
                    SectionGatherPasFlow secPasFlow = searchSecPasList.Find(item => item.SectionPasFlow.BelongSecKSP.strSecName == strSecName).SectionPasFlow;
                    SectionGatherPasFlowPerHour secHourPasFlow = secPasFlow.SectionPasFlowList_Hour.Find(item => item.FluxStartDateTime <= dtSecTime && item.FluxLastDateTime > dtSecTime);
                    SectionGatherPasFlowMinuteSpan secMinutePasFlow = null;
                    if (secHourPasFlow != null)
                    {
                        secMinutePasFlow = secHourPasFlow.SectionPasFlowList_Min.Find(item => item.FluxStartDateTime <= dtSecTime && item.FluxLastDateTime > dtSecTime);
                    }
                    int iPasNum = 0;
                    if (secMinutePasFlow != null)
                    {
                        iPasNum = secMinutePasFlow.PassengerNum;

                    }
                    else
                    {

                    }
                    iPasNumList[i] += iPasNum;
                }
                iMaxSecPas = iPasNumList.Max();
                int iMaxSecIndex = iPasNumList.FindIndex(item => item == iMaxSecPas);
                string strMaxSec = strSecNameList[iMaxSecIndex];
                strPasInfo = "  " + strMaxSec + "  " + dtSecStartTimeList[iMaxSecIndex].ToLongTimeString() + "  " + iMaxSecPas;
                dTrainNum = iMaxSecPas * 1.00 / BelongedLine.VehicleCapacity;
                iTimeLength += Math.Abs(iBasicLength);
                if (dTrainNum >= 1 || iTimeLength >= BelongedLine.iLineMaxItvl)
                {
                    break;
                }
            }
            //Debug.Write(strPasInfo);
            if (dTrainNum > 0)
            {
                itvl = Convert.ToInt32(Math.Round(iTimeLength / dTrainNum, 0));
            }
            else
            {
                itvl = iTimeLength;
            }
            if (itvl < timeOperInfo.iMinTrainInterval)
                itvl = timeOperInfo.iMinTrainInterval;
            else if (itvl > timeOperInfo.iLineMaxRunCstr)
                itvl = timeOperInfo.iLineMaxRunCstr;
            timeOperInfo.iMinTrainInterval = itvl;
            if (bIsLeft)
            {
                itvl = -itvl;
            }
            return itvl;
        }
        private void BuildRelationTrainListAndDiagramStation()//建立站名线与生成列车运行线之间的关系
        {
            //与站名线进行关联
            for (int i = 0; i < CurrentTrainDiagram.TrainDiagramTimeTableList.Count; i++)
            {
                TrainDiagramTimeTableStructure traDiaTimeTable = CurrentTrainDiagram.TrainDiagramTimeTableList[i];
                if (i == 576)
                {

                }
                traDiaTimeTable.StationTrainLineList.Sort();
                traDiaTimeTable.SetSectionTrainLine(CurrentTrainDiagram.BelongedLine);
                CurrentTrainDiagram.LinkTrainDiagramStationToTimeTable(traDiaTimeTable);
            }
        }
        private void InputTrainDiagramStationPass()
        {
            for (int i = 0; i < CurrentTrainDiagram.TrainDiagramStationList.Count; i++)
            {
                TrainDiagramStationStructure trainStaion = CurrentTrainDiagram.TrainDiagramStationList[i];
                string strDownStaInfo = trainStaion.StationName + ":";
                string strUpStaInfo = trainStaion.StationName + ":";
                for (int j = 0; j < trainStaion.StationTrainList_Down.Count; j++)
                {
                    StationTrainLineStructure downPassTrainLine = trainStaion.StationTrainList_Down[j];
                    strDownStaInfo += downPassTrainLine.StationTime.strArrTime + "-" + downPassTrainLine.StationTime.strDepTime + "  ";
                }
                for (int j = 0; j < trainStaion.StationTrainList_Up.Count; j++)
                {
                    StationTrainLineStructure upPassTrainLine = trainStaion.StationTrainList_Up[j];
                    strUpStaInfo += upPassTrainLine.StationTime.strArrTime + "-" + upPassTrainLine.StationTime.strDepTime + "  ";
                }
                Debug.WriteLine(strDownStaInfo);
                Debug.WriteLine(strUpStaInfo);
            }
        }
        #endregion 

        #region 基于运营方案计算等待时间成本  
        public List<DiagramRoute> DownTrainList;
        public List<DiagramRoute> UpTrainList;
        List<DiagramRoute> DownRouteList;
        List<DiagramRoute> UpRouteList;
        public double CalWaitTimeCost(List<AFCPassengerDataStructure> ODPasDataList)
        {
            double dPasWaitTime = 0;
            InitialParamter2();
            CurrentTrainDiagram.TrainDiagramTimeTableList.Clear();
            GnrtTrainDiagram2();
            CurrentTrainDiagram.SetDiagramPassbyStation();
            //InputTrainDiagramStationPass();
            int iPasNum = 0;
            List<AFCPassengerDataStructure> odPasDataList = ODPasDataList;
            for (int i = 0; i < odPasDataList.Count; i++)
            {
                AFCPassengerDataStructure odPas = odPasDataList[i];
                odPas.dtEnterTime = odPas.SetStrtimeToDatetime(DateTime.Now.ToString("yyyyMMdd"), odPas.InStationTime);
                TrainDiagramStationStructure oriTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.OriStationName);
                TrainDiagramStationStructure desTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.DesStationName);
                if (oriTrainDiagramSta != null && desTrainDiagramSta != null)
                {
                    int oriStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.OriStationName);
                    int desStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.DesStationName);
                    bool bIsDown = true;
                    if (oriStaIndex > desStaIndex) bIsDown = false;
                    List<StationTrainLineStructure> searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Down;
                    if (!bIsDown) searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Up;
                    DateTime staRightTime = searchStaTrainLine[searchStaTrainLine.Count - 1].StationTime.DepDateTime;
                    //DateTime staLeftTime = searchStaTrainLine[0].StationTime.ArrDateTime;
                    if (odPas.dtEnterTime < staRightTime)
                    {
                        StationTrainLineStructure selectTrain = searchStaTrainLine.Find(item => item.StationTime.DepDateTime > odPas.dtEnterTime);
                        dPasWaitTime += (selectTrain.StationTime.DepDateTime - odPas.dtEnterTime).TotalSeconds;
                        iPasNum++;
                    }
                    else
                    {
                        continue;
                    }
                }
                else
                {

                }
            }
            dPasWaitTime = dPasWaitTime * c3 * dWeight;
            return dPasWaitTime;
        }
        private void InitialParamter2()
        {
            CurTimeOper.dtStartTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "05:30:00");
            CurTimeOper.dtLastTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "12:00:00");

            BelongedLine = CurCapRsceAllocPro.BelongedLine;
            DownRouteList = new List<DiagramRoute>();

            for (int i = 0; i < DownTrainList.Count; i++)
            {
                DiagramRoute trainRoute = DownTrainList[i];
                if (!DownRouteList.Exists(item => item.RouteName == trainRoute.RouteName))
                {
                    DownRouteList.Add(trainRoute);
                }
            }

            if (DownRouteList.Count > 1)
            {
                List<DiagramRoute> trainOrderRouteList = new List<DiagramRoute>();//需要进行重新排序
                DownRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
                {
                    return route1.RouteStationList.Count.CompareTo(route2.RouteStationList.Count);
                });

                List<int> rotueDownNumList = new List<int>();

                for (int i = 0; i < DownRouteList.Count; i++)
                {
                    DiagramRoute route = DownRouteList[i];
                    int iRouteNum = 0;
                    for (int j = 0; j < DownTrainList.Count; j++)
                    {
                        DiagramRoute trainRoute = DownTrainList[j];
                        if (trainRoute.RouteName == route.RouteName)
                        {
                            iRouteNum++;
                        }
                    }
                    rotueDownNumList.Add(iRouteNum);
                }

                int iCheckNum = 0;
                List<int> difDownRouteNum = new List<int>();
                for (int i = 0; i < rotueDownNumList.Count; i++)
                {
                    if (!difDownRouteNum.Exists(item => item == rotueDownNumList[i]))
                    {
                        difDownRouteNum.Add(rotueDownNumList[i]);
                    }
                }
                iCheckNum = difDownRouteNum.Count;
                List<DiagramRoute> orderRoute = new List<DiagramRoute>(DownRouteList);
                for (int i = 0; i < iCheckNum; i++)
                {
                    int iMinRoute = rotueDownNumList.Min();
                    for (int j = 0; j < iMinRoute; j++)
                    {
                        for (int k = 0; k < orderRoute.Count; k++)
                        {
                            DiagramRoute trainRoute = orderRoute[k];
                            trainOrderRouteList.Add(trainRoute);
                        }
                    }
                    for (int j = 0; j < rotueDownNumList.Count; j++)
                    {
                        rotueDownNumList[j] -= iMinRoute;
                    }
                    if (i != iCheckNum - 1)
                    {
                        while (rotueDownNumList.Exists(item => item == 0))
                        {
                            int iRemoveIndex = rotueDownNumList.FindIndex(item => item == 0);
                            orderRoute.Remove(orderRoute[iRemoveIndex]);
                            rotueDownNumList.Remove(0);
                        }
                    }
                }
                DownTrainList = new List<DiagramRoute>(trainOrderRouteList);
            }

            UpRouteList = new List<DiagramRoute>();

            for (int i = 0; i < UpTrainList.Count; i++)
            {
                DiagramRoute trainRoute = UpTrainList[i];
                if (!UpRouteList.Exists(item => item.RouteName == trainRoute.RouteName))
                {
                    UpRouteList.Add(trainRoute);
                }
            }

            if (UpRouteList.Count > 1)
            {
                List<DiagramRoute> trainOrderRouteList = new List<DiagramRoute>();//需要进行重新排序
                UpRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
                {
                    return route1.RouteStationList.Count.CompareTo(route2.RouteStationList.Count);
                });

                List<int> rotueUpNumList = new List<int>();

                for (int i = 0; i < UpRouteList.Count; i++)
                {
                    DiagramRoute route = UpRouteList[i];
                    int iRouteNum = 0;
                    for (int j = 0; j < UpTrainList.Count; j++)
                    {
                        DiagramRoute trainRoute = UpTrainList[j];
                        if (trainRoute.RouteName == route.RouteName)
                        {
                            iRouteNum++;
                        }
                    }
                    rotueUpNumList.Add(iRouteNum);
                }

                int iCheckNum = 0;
                List<int> difUpRouteNum = new List<int>();
                for (int i = 0; i < rotueUpNumList.Count; i++)
                {
                    if (!difUpRouteNum.Exists(item => item == rotueUpNumList[i]))
                    {
                        difUpRouteNum.Add(rotueUpNumList[i]);
                    }
                }
                iCheckNum = difUpRouteNum.Count;
                List<DiagramRoute> orderRoute = new List<DiagramRoute>(UpRouteList);
                for (int i = 0; i < iCheckNum; i++)
                {
                    int iMinRoute = rotueUpNumList.Min();
                    for (int j = 0; j < iMinRoute; j++)
                    {
                        for (int k = 0; k < orderRoute.Count; k++)
                        {
                            DiagramRoute trainRoute = orderRoute[k];
                            trainOrderRouteList.Add(trainRoute);
                        }
                    }
                    for (int j = 0; j < rotueUpNumList.Count; j++)
                    {
                        rotueUpNumList[j] -= iMinRoute;
                    }
                    if (i != iCheckNum - 1)
                    {
                        while (rotueUpNumList.Exists(item => item == 0))
                        {
                            int iRemoveIndex = rotueUpNumList.FindIndex(item => item == 0);
                            orderRoute.Remove(orderRoute[iRemoveIndex]);
                            rotueUpNumList.Remove(0);
                        }
                    }
                }
                UpTrainList = new List<DiagramRoute>(trainOrderRouteList);
            }
        }
        private void GnrtTrainDiagram2()
        {
            //bIsLeft 是否是从右向左进行列车运行线生成
            bool bIsLeft = true;
            List<TrainDiagramTimeTableStructure> gnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            SectionRunScale secRunScale = CurTimeOper.TimeSecRunScale;
            StationStopScale staStopScale = CurTimeOper.TimeStaStopScale;
            TrainDiagramTimeTableStructure srdDownTrain = BehTimeOperInfo.DownTrainList[0];
            gnrtTrainList.Add(srdDownTrain);
            DateTime dtStartTime = srdDownTrain.dtVirtStartTime;
            CurTimeOper.iMinTrainInterval = BehTimeOperInfo.TimeSustainSecond / BehTimeOperInfo.DownTrainList.Count;
            //Debug.WriteLine("下行");
            int iTrainIndex = 0;
            double dRunInterval = CalTrainItvlBySecPas(srdDownTrain, CurTimeOper, bIsLeft);
            //Debug.WriteLine(iTrainIndex +"  "+ dRunInterval);
            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            DateTime dtLastTime = CurTimeOper.dtStartTime;
           
            List<DiagramRoute> timeCalRouteCalList = DownRouteList;
            DownRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
            {
                return route2.RouteStationList.Count.CompareTo(route1.RouteStationList.Count);
            });
            List<DateTime> trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            for (int i = 0; i < DownTrainList.Count; i++)
            {
                DiagramRoute useRoute = DownTrainList[i];
                int iTimeIndex = DownRouteList.FindIndex(item => item.RouteName == useRoute.RouteName);
                DateTime dtTrainStartTime = trainStartTimeList[iTimeIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, CurTimeOper, dtTrainStartTime, dtStartTime);
                gnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= CurTimeOper.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(CurTimeOper, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int j = 0; j < trainStartTimeList.Count; j++)
                        {
                            trainStartTimeList[i] = trainStartTimeList[j].AddSeconds(iOffset);
                        }
                    }
                }
                dRunInterval = CalTrainItvlBySecPas(train, CurTimeOper, bIsLeft);
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int j = 0; j < trainStartTimeList.Count; j++)
                {
                    trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(dRunInterval);
                }
            }

            //绘制非主要列车运营方向的列车运行线
            List<TrainDiagramTimeTableStructure> rvseGnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            TrainDiagramTimeTableStructure srdUpTrain = BehTimeOperInfo.UpTrainList[0];
            rvseGnrtTrainList.Add(srdUpTrain);
            CurTimeOper.iMinTrainInterval = BehTimeOperInfo.TimeSustainSecond / BehTimeOperInfo.UpTrainList.Count;
            dtStartTime = srdUpTrain.dtVirtStartTime;
            //Debug.WriteLine("上行");
            iTrainIndex = 0;
            dRunInterval = CalTrainItvlBySecPas(srdUpTrain, CurTimeOper, bIsLeft);
            //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            timeCalRouteCalList = UpRouteList;
            UpRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
            {
                return route2.RouteStationList.Count.CompareTo(route1.RouteStationList.Count);
            });
            trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            iTrainIndex = 0;
            for (int i = 0; i < UpTrainList.Count; i++)
            {
                DiagramRoute useRoute = UpTrainList[i];
                int iTimeIndex = UpRouteList.FindIndex(item => item.RouteName == useRoute.RouteName);
                DateTime dtTrainStartTime = trainStartTimeList[iTimeIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, CurTimeOper, dtTrainStartTime, dtStartTime);
                rvseGnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= CurTimeOper.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(CurTimeOper, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int j = 0; j < trainStartTimeList.Count; j++)
                        {
                            trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(iOffset);
                        }
                    }
                }
                dRunInterval = CalTrainItvlBySecPas(train, CurTimeOper, bIsLeft);
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int j = 0; j < trainStartTimeList.Count; j++)
                {
                    trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(dRunInterval);
                }
            }

            //将生成的列车运行线添加到分时集合中
            if (bIsLeft)
            {
                gnrtTrainList.Reverse();
                rvseGnrtTrainList.Reverse();
            }
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(gnrtTrainList);
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(rvseGnrtTrainList);
            CurTimeOper.DownTrainList.Clear();
            CurTimeOper.UpTrainList.Clear();
            CurTimeOper.DownTrainList.AddRange(gnrtTrainList);
            CurTimeOper.UpTrainList.AddRange(rvseGnrtTrainList);
            BuildRelationTrainListAndDiagramStation();
        }
        
        #endregion

        #region 基于固定行车间隔计算等待时间成本
        int iFixItvl = 0;
        public double CalWaitTimeCost_FixItvl(List<AFCPassengerDataStructure> ODPasDataList)
        {
            double dPasWaitTime = 0;
            InitialParamter3();
            CurrentTrainDiagram.TrainDiagramTimeTableList.Clear();
            GnrtTrainDiagram3();
            CurrentTrainDiagram.SetDiagramPassbyStation();
            //InputTrainDiagramStationPass();
            int iPasNum = 0;
            List<AFCPassengerDataStructure> odPasDataList = ODPasDataList;
            for (int i = 0; i < odPasDataList.Count; i++)
            {
                AFCPassengerDataStructure odPas = odPasDataList[i];
                odPas.dtEnterTime = odPas.SetStrtimeToDatetime(DateTime.Now.ToString("yyyyMMdd"), odPas.InStationTime);
                TrainDiagramStationStructure oriTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.OriStationName);
                TrainDiagramStationStructure desTrainDiagramSta = CurrentTrainDiagram.TrainDiagramStationList.Find(item => item.StationName == odPas.DesStationName);
                if (oriTrainDiagramSta != null && desTrainDiagramSta != null)
                {
                    int oriStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.OriStationName);
                    int desStaIndex = CurrentTrainDiagram.TrainDiagramStationList.FindIndex(item => item.StationName == odPas.DesStationName);
                    bool bIsDown = true;
                    if (oriStaIndex > desStaIndex) bIsDown = false;
                    List<StationTrainLineStructure> searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Down;
                    if (!bIsDown) searchStaTrainLine = oriTrainDiagramSta.StationTrainList_Up;
                    DateTime staRightTime = searchStaTrainLine[searchStaTrainLine.Count - 1].StationTime.DepDateTime;
                    //DateTime staLeftTime = searchStaTrainLine[0].StationTime.ArrDateTime;
                    if (odPas.dtEnterTime < staRightTime)
                    {
                        StationTrainLineStructure selectTrain = searchStaTrainLine.Find(item => item.StationTime.DepDateTime > odPas.dtEnterTime);
                        dPasWaitTime += (selectTrain.StationTime.DepDateTime - odPas.dtEnterTime).TotalSeconds;
                        iPasNum++;
                    }
                    else
                    {
                        continue;
                    }
                }
                else
                {

                }
            }
            dPasWaitTime = dPasWaitTime * c3 * dWeight;
            return dPasWaitTime;
        }
        private void InitialParamter3()
        {
            iFixItvl = CurTimeOper.TimeSustainSecond / DownTrainList.Count;
            iFixItvl = -1 * iFixItvl;

            BelongedLine = CurCapRsceAllocPro.BelongedLine;
            DownRouteList = new List<DiagramRoute>();

            for (int i = 0; i < DownTrainList.Count; i++)
            {
                DiagramRoute trainRoute = DownTrainList[i];
                if (!DownRouteList.Exists(item => item.RouteName == trainRoute.RouteName))
                {
                    DownRouteList.Add(trainRoute);
                }
            }

            if (DownRouteList.Count > 1)
            {
                List<DiagramRoute> trainOrderRouteList = new List<DiagramRoute>();//需要进行重新排序
                DownRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
                {
                    return route1.RouteStationList.Count.CompareTo(route2.RouteStationList.Count);
                });

                List<int> rotueDownNumList = new List<int>();

                for (int i = 0; i < DownRouteList.Count; i++)
                {
                    DiagramRoute route = DownRouteList[i];
                    int iRouteNum = 0;
                    for (int j = 0; j < DownTrainList.Count; j++)
                    {
                        DiagramRoute trainRoute = DownTrainList[j];
                        if (trainRoute.RouteName == route.RouteName)
                        {
                            iRouteNum++;
                        }
                    }
                    rotueDownNumList.Add(iRouteNum);
                }

                int iCheckNum = 0;
                List<int> difDownRouteNum = new List<int>();
                for (int i = 0; i < rotueDownNumList.Count; i++)
                {
                    if (!difDownRouteNum.Exists(item => item == rotueDownNumList[i]))
                    {
                        difDownRouteNum.Add(rotueDownNumList[i]);
                    }
                }
                iCheckNum = difDownRouteNum.Count;
                List<DiagramRoute> orderRoute = new List<DiagramRoute>(DownRouteList);
                for (int i = 0; i < iCheckNum; i++)
                {
                    int iMinRoute = rotueDownNumList.Min();
                    for (int j = 0; j < iMinRoute; j++)
                    {
                        for (int k = 0; k < orderRoute.Count; k++)
                        {
                            DiagramRoute trainRoute = orderRoute[k];
                            trainOrderRouteList.Add(trainRoute);
                        }
                    }
                    for (int j = 0; j < rotueDownNumList.Count; j++)
                    {
                        rotueDownNumList[j] -= iMinRoute;
                    }
                    if (i != iCheckNum - 1)
                    {
                        while (rotueDownNumList.Exists(item => item == 0))
                        {
                            int iRemoveIndex = rotueDownNumList.FindIndex(item => item == 0);
                            orderRoute.Remove(orderRoute[iRemoveIndex]);
                            rotueDownNumList.Remove(0);
                        }
                    }
                }
                DownTrainList = new List<DiagramRoute>(trainOrderRouteList);
            }

            UpRouteList = new List<DiagramRoute>();

            for (int i = 0; i < UpTrainList.Count; i++)
            {
                DiagramRoute trainRoute = UpTrainList[i];
                if (!UpRouteList.Exists(item => item.RouteName == trainRoute.RouteName))
                {
                    UpRouteList.Add(trainRoute);
                }
            }

            if (UpRouteList.Count > 1)
            {
                List<DiagramRoute> trainOrderRouteList = new List<DiagramRoute>();//需要进行重新排序
                UpRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
                {
                    return route1.RouteStationList.Count.CompareTo(route2.RouteStationList.Count);
                });

                List<int> rotueUpNumList = new List<int>();

                for (int i = 0; i < UpRouteList.Count; i++)
                {
                    DiagramRoute route = UpRouteList[i];
                    int iRouteNum = 0;
                    for (int j = 0; j < UpTrainList.Count; j++)
                    {
                        DiagramRoute trainRoute = UpTrainList[j];
                        if (trainRoute.RouteName == route.RouteName)
                        {
                            iRouteNum++;
                        }
                    }
                    rotueUpNumList.Add(iRouteNum);
                }

                int iCheckNum = 0;
                List<int> difUpRouteNum = new List<int>();
                for (int i = 0; i < rotueUpNumList.Count; i++)
                {
                    if (!difUpRouteNum.Exists(item => item == rotueUpNumList[i]))
                    {
                        difUpRouteNum.Add(rotueUpNumList[i]);
                    }
                }
                iCheckNum = difUpRouteNum.Count;
                List<DiagramRoute> orderRoute = new List<DiagramRoute>(UpRouteList);
                for (int i = 0; i < iCheckNum; i++)
                {
                    int iMinRoute = rotueUpNumList.Min();
                    for (int j = 0; j < iMinRoute; j++)
                    {
                        for (int k = 0; k < orderRoute.Count; k++)
                        {
                            DiagramRoute trainRoute = orderRoute[k];
                            trainOrderRouteList.Add(trainRoute);
                        }
                    }
                    for (int j = 0; j < rotueUpNumList.Count; j++)
                    {
                        rotueUpNumList[j] -= iMinRoute;
                    }
                    if (i != iCheckNum - 1)
                    {
                        while (rotueUpNumList.Exists(item => item == 0))
                        {
                            int iRemoveIndex = rotueUpNumList.FindIndex(item => item == 0);
                            orderRoute.Remove(orderRoute[iRemoveIndex]);
                            rotueUpNumList.Remove(0);
                        }
                    }
                }
                UpTrainList = new List<DiagramRoute>(trainOrderRouteList);
            }
            CurTimeOper.dtStartTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "05:30:00");
            CurTimeOper.dtLastTime = Convert.ToDateTime(DateTime.Now.ToLongDateString() + " " + "12:00:00");
        }
        private void GnrtTrainDiagram3()
        {
            //bIsLeft 是否是从右向左进行列车运行线生成
            int iTime = 5400;
            bool bIsLeft = true;
            List<TrainDiagramTimeTableStructure> gnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            SectionRunScale secRunScale = CurTimeOper.TimeSecRunScale;
            StationStopScale staStopScale = CurTimeOper.TimeStaStopScale;
            TrainDiagramTimeTableStructure srdDownTrain = BehTimeOperInfo.DownTrainList[0];
            gnrtTrainList.Add(srdDownTrain);
            DateTime dtStartTime = srdDownTrain.dtVirtStartTime;
            CurTimeOper.iMinTrainInterval = BehTimeOperInfo.TimeSustainSecond / BehTimeOperInfo.DownTrainList.Count;
            iFixItvl = iTime / DownTrainList.Count;
            iFixItvl = -1 * iFixItvl;
            double dRunInterval = iFixItvl;

            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            DateTime dtLastTime = CurTimeOper.dtStartTime;
            int iTrainIndex = 0;
            List<DiagramRoute> timeCalRouteCalList = DownRouteList;
            DownRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
            {
                return route2.RouteStationList.Count.CompareTo(route1.RouteStationList.Count);
            });
            List<DateTime> trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            for (int i = 0; i < DownTrainList.Count; i++)
            {
                DiagramRoute useRoute = DownTrainList[i];
                int iTimeIndex = DownRouteList.FindIndex(item => item.RouteName == useRoute.RouteName);
                DateTime dtTrainStartTime = trainStartTimeList[iTimeIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, CurTimeOper, dtTrainStartTime, dtStartTime);
                gnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= CurTimeOper.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(CurTimeOper, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int j = 0; j < trainStartTimeList.Count; j++)
                        {
                            trainStartTimeList[i] = trainStartTimeList[j].AddSeconds(iOffset);
                        }
                    }
                }
                dRunInterval = iFixItvl;
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int j = 0; j < trainStartTimeList.Count; j++)
                {
                    trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(dRunInterval);
                }
            }

            //绘制非主要列车运营方向的列车运行线
            List<TrainDiagramTimeTableStructure> rvseGnrtTrainList = new List<TrainDiagramTimeTableStructure>();
            TrainDiagramTimeTableStructure srdUpTrain = BehTimeOperInfo.UpTrainList[0];
            rvseGnrtTrainList.Add(srdUpTrain);
            CurTimeOper.iMinTrainInterval = BehTimeOperInfo.TimeSustainSecond / BehTimeOperInfo.UpTrainList.Count;
            dtStartTime = srdUpTrain.dtVirtStartTime;
            iFixItvl = iTime / UpTrainList.Count;
            iFixItvl = -1 * iFixItvl;
            dRunInterval = iFixItvl;
            dtStartTime = dtStartTime.AddSeconds(dRunInterval);
            timeCalRouteCalList = UpRouteList;
            UpRouteList.Sort(delegate (DiagramRoute route1, DiagramRoute route2)
            {
                return route2.RouteStationList.Count.CompareTo(route1.RouteStationList.Count);
            });
            trainStartTimeList = CalTrainStartTimeList(timeCalRouteCalList, secRunScale, staStopScale, dtStartTime);
            iTrainIndex = 0;
            for (int i = 0; i < UpTrainList.Count; i++)
            {
                DiagramRoute useRoute = UpTrainList[i];
                int iTimeIndex = UpRouteList.FindIndex(item => item.RouteName == useRoute.RouteName);
                DateTime dtTrainStartTime = trainStartTimeList[iTimeIndex];
                TrainDiagramTimeTableStructure train = GenerateSingleTrainTimeTable(useRoute, CurTimeOper, dtTrainStartTime, dtStartTime);
                rvseGnrtTrainList.Add(train);
                //更新参数
                iTrainIndex++;
                if (iTrainIndex <= CurTimeOper.iTotalRouteNum)//针对第一个周期的列车运行线进行检验
                {
                    int iOffset = FirPeriodGnrtTrainTimeAdjust(CurTimeOper, train, bIsLeft);
                    if (iOffset != 0)
                    {
                        TrainTimeAdjust(train, iOffset);
                        dtStartTime = dtStartTime.AddSeconds(iOffset);
                        for (int j = 0; j < trainStartTimeList.Count; j++)
                        {
                            trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(iOffset);
                        }
                    }
                }
                dRunInterval = iFixItvl;
                //Debug.WriteLine(iTrainIndex + "  " + dRunInterval);
                dtStartTime = dtStartTime.AddSeconds(dRunInterval);
                for (int j = 0; j < trainStartTimeList.Count; j++)
                {
                    trainStartTimeList[j] = trainStartTimeList[j].AddSeconds(dRunInterval);
                }
            }

            //将生成的列车运行线添加到分时集合中
            if (bIsLeft)
            {
                gnrtTrainList.Reverse();
                rvseGnrtTrainList.Reverse();
            }
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(gnrtTrainList);
            CurrentTrainDiagram.TrainDiagramTimeTableList.AddRange(rvseGnrtTrainList);
            CurTimeOper.DownTrainList.Clear();
            CurTimeOper.UpTrainList.Clear();
            CurTimeOper.DownTrainList.AddRange(gnrtTrainList);
            CurTimeOper.UpTrainList.AddRange(rvseGnrtTrainList);
            BuildRelationTrainListAndDiagramStation();
        }
        #endregion
    }
}
