"""核心算法自测：与暴力枚举全部时刻组合的结果交叉验证。

运行：python3 tests.py
"""
import itertools
import random

from core import (compute_alerts, counterexample, max_matching, min_hits,
                  solve)


def brute_max_matching(combo, alerts, L, U):
    """增广路求二分图最大匹配（暴力，供对照）。"""
    adj = []
    for t in combo:
        lo, hi = t - U, t - L
        adj.append([a for a in alerts if lo <= a <= hi])
    match_of_alert = {}

    def aug(i, seen):
        for a in adj[i]:
            if a in seen:
                continue
            seen.add(a)
            if a not in match_of_alert or aug(match_of_alert[a], seen):
                match_of_alert[a] = i
                return True
        return False

    cnt = 0
    for i in range(len(combo)):
        if aug(i, set()):
            cnt += 1
    return cnt


def brute_min_hits(L, alerts, intervals, U):
    """枚举全部时刻组合，取最大配对数的最小值（暴力，供对照）。"""
    best = None
    for combo in itertools.product(*[range(a, b + 1) for a, b in intervals]):
        v = brute_max_matching(list(combo), alerts, L, U)
        best = v if best is None else min(best, v)
    return best


def test_compute_alerts():
    minutes = [10, 11, 12, 13, 14, 15, 16, 17]
    scores = [5, 9, 9, 8, 2, 8, 7, 1]
    assert compute_alerts(minutes, scores, 8) == [11, 15]
    assert compute_alerts(minutes, scores, 10) == []
    assert compute_alerts(minutes, scores, 1) == [10]  # 整段只在首分钟告警
    print("ok  compute_alerts")


def test_max_matching_vs_brute(rng, trials=300):
    for _ in range(trials):
        n = rng.randint(0, 12)
        alerts = sorted(rng.sample(range(0, 40), n))
        m = rng.randint(1, 5)
        U = rng.randint(1, 8)
        L = rng.randint(1, U)
        combo = [rng.randint(0, 40) for _ in range(m)]
        g = len(max_matching(combo, alerts, L, U))
        b = brute_max_matching(combo, alerts, L, U)
        assert g == b, (combo, alerts, L, U, g, b)
    print("ok  max_matching == brute_max_matching")


def test_min_hits_vs_brute(rng, trials=400):
    for _ in range(trials):
        n = rng.randint(0, 10)
        alerts = sorted(rng.sample(range(0, 30), n))
        m = rng.randint(1, 4)
        U = rng.randint(1, 7)
        L = rng.randint(1, U)
        # 互不重叠的小区间
        intervals = []
        cur = rng.randint(0, 3)
        for _ in range(m):
            a = cur
            b = a + rng.randint(0, 3)
            intervals.append((a, b))
            cur = b + rng.randint(1, 4)
        got = min_hits(L, alerts, intervals, U)
        want = brute_min_hits(L, alerts, intervals, U)
        assert got == want, (L, alerts, intervals, U, got, want)
        # 反例组合的配对数应恰好等于 min_hits
        combo, pairs = counterexample(L, alerts, intervals, U)
        assert len(pairs) == want, (L, alerts, intervals, U, combo, pairs, want)
        # 反例组合必须取自各区间
        for (a, b), t in zip(intervals, combo):
            assert a <= t <= b
    print("ok  min_hits/counterexample == brute force (400 组随机)")


def test_solve_vs_linear(rng, trials=120):
    for _ in range(trials):
        n = rng.randint(0, 10)
        alerts = sorted(rng.sample(range(0, 30), n))
        m = rng.randint(1, 4)
        U = rng.randint(1, 8)
        K = rng.randint(1, m + 2)
        intervals = []
        cur = rng.randint(0, 3)
        for _ in range(m):
            a = cur
            b = a + rng.randint(0, 3)
            intervals.append((a, b))
            cur = b + rng.randint(1, 4)
        res = solve(alerts, intervals, U, K)
        # 线性扫描对照
        mh = {L: brute_min_hits(L, alerts, intervals, U) for L in range(1, U + 1)}
        feasible = [L for L in range(1, U + 1) if mh[L] >= K]
        if not feasible:
            assert res["status"] == "infeasible", (res, mh, K)
            c = res["counter"]
            assert c["L"] == 1 and c["hits"] == mh[1] < K
        else:
            Lstar = max(feasible)
            assert res["status"] == "ok" and res["L"] == Lstar, (res, mh, K)
            assert res["min_hits"] == mh[Lstar]
            if Lstar < U:
                c = res["counter"]
                assert c["L"] == Lstar + 1 and c["hits"] == mh[Lstar + 1] < K
            else:
                assert "counter" not in res
    print("ok  solve == 线性扫描暴力解 (120 组随机)")


def test_monotonicity(rng, trials=60):
    for _ in range(trials):
        n = rng.randint(0, 12)
        alerts = sorted(rng.sample(range(0, 40), n))
        m = rng.randint(1, 5)
        U = rng.randint(1, 10)
        intervals = []
        cur = rng.randint(0, 3)
        for _ in range(m):
            a = cur
            b = a + rng.randint(0, 3)
            intervals.append((a, b))
            cur = b + rng.randint(1, 4)
        seq = [min_hits(L, alerts, intervals, U) for L in range(1, U + 1)]
        assert all(seq[i] >= seq[i + 1] for i in range(len(seq) - 1)), seq
    print("ok  min_hits 关于 L 单调不增")


def test_edge_cases():
    # 无告警 -> 无法承诺
    res = solve([], [(10, 12)], 5, 1)
    assert res["status"] == "infeasible" and res["counter"]["hits"] == 0
    # K 大于卡纸数 -> 无法承诺（告警 6/7/8 能覆盖 [10,12] 的任一时刻，但最多配对 1 次）
    res = solve([6, 7, 8], [(10, 12)], 5, 2)
    assert res["status"] == "infeasible" and res["counter"]["hits"] == 1
    # 告警远早于所有卡纸（提前量永远不够）-> 无法承诺
    res = solve([1, 2], [(100, 105)], 5, 1)
    assert res["status"] == "infeasible"
    # 告警提前量为 3/4/5 分钟 -> 最大可承诺 L=5，L=6 档反例配对 0 次
    res = solve([95, 96, 97], [(100, 100)], 10, 1)
    assert res["status"] == "ok" and res["L"] == 5
    assert res["counter"]["L"] == 6 and res["counter"]["hits"] == 0
    # 告警恰好都在窗口内 -> L 可取到 U
    res = solve([90], [(100, 100)], 10, 1)
    assert res["status"] == "ok" and res["L"] == 10 and "counter" not in res
    # U 大于可达提前量时被截断，且给出 L+1 反例
    res = solve([90], [(100, 100)], 50, 1)
    assert res["status"] == "ok" and res["L"] == 10
    assert res["counter"]["L"] == 11 and res["counter"]["hits"] == 0
    print("ok  边界情形")


def test_web_app():
    """用 Flask 测试客户端走通：上传 -> 核定 -> 更正撤下 -> 无法承诺 -> 校验拦截。"""
    import io as _io

    import app as web
    from sample_data import to_csv

    web.app.config.update(TESTING=True)
    c = web.app.test_client()
    assert c.get("/").status_code == 200
    assert len(c.get("/sample.csv").data.decode().strip().splitlines()) == 721

    # 上传示例数据
    r = c.post("/upload", data={"file": (_io.BytesIO(to_csv().encode()), "s.csv")},
               content_type="multipart/form-data", follow_redirects=True)
    assert "已加载" in r.get_data(as_text=True)

    # 演示参数：可承诺 L=60，L=61 档反例命中 4 次
    iv = "125-130\n250-254\n370-374\n480-484\n600-604\n705-709"
    r = c.post("/analyze", data={"threshold": "80", "U": "90", "K": "5",
                                 "intervals": iv}, follow_redirects=True)
    html = r.get_data(as_text=True)
    assert "可承诺：L = 60 分钟" in html
    assert "任意卡纸时刻组合至少命中 5 次" in html
    assert "合计命中 4 次（共 6 次卡纸）" in html

    # 更正区间：旧结论撤下并出现在历史
    r = c.post("/analyze", data={"threshold": "80", "U": "90", "K": "5",
                                 "intervals": "126-130\n250-254\n370-374\n480-484\n600-604\n705-709"},
               follow_redirects=True)
    html = r.get_data(as_text=True)
    assert "已撤下" in html and "参数或卡纸区间已更正" in html

    # K=7 超过卡纸数：无法承诺
    r = c.post("/analyze", data={"threshold": "80", "U": "90", "K": "7",
                                 "intervals": iv}, follow_redirects=True)
    assert "无法承诺" in r.get_data(as_text=True)

    # 非法输入被拦截
    r = c.post("/upload", data={"file": (_io.BytesIO(b"minute,score\n1,50\n3,60\n"), "b.csv")},
               content_type="multipart/form-data", follow_redirects=True)
    assert "分钟号不连续" in r.get_data(as_text=True)
    r = c.post("/analyze", data={"threshold": "80", "U": "90", "K": "5",
                                 "intervals": "125-130\n128-135"},
               follow_redirects=True)
    assert "重叠" in r.get_data(as_text=True)
    print("ok  网页端冒烟测试")


def test_threshold_precision_web():
    """阈值按输入十进制精确比较：80.000000000000001 不能把 80 分判为达标。"""
    import io as _io
    import re

    import app as web

    web.app.config.update(TESTING=True)
    c = web.app.test_client()
    # 分钟 10-12 为 80 分，14-18 为 95 分；阈值 80 时告警 [10,14]，
    # 阈值 80.000000000000001 时告警只剩 [14]。
    rows = []
    for i in range(1, 31):
        s = 80 if 10 <= i <= 12 else (95 if 14 <= i <= 18 else 0)
        rows.append(f"{i},{s}")
    text = "minute,score\n" + "\n".join(rows) + "\n"
    c.post("/upload", data={"file": (_io.BytesIO(text.encode()), "t.csv")},
           content_type="multipart/form-data")

    def run(t):
        r = c.post("/analyze", data={"threshold": t, "U": "20", "K": "1",
                                     "intervals": "25-26"},
                   follow_redirects=True)
        return r.get_data(as_text=True)

    html = run("80")
    assert "本档参数下共 2 条告警" in html
    assert "可承诺：L = 15 分钟" in html

    html = run("80.000000000000001")
    assert "本档参数下共 1 条告警" in html
    assert "可承诺：L = 11 分钟" in html
    # 表单与当前结论保留输入的精确阈值
    assert 'name="threshold" value="80.000000000000001"' in html
    assert "阈值 80.000000000000001" in html

    # 科学计数法按十进制精确值解释
    assert "可承诺：L = 15 分钟" in run("8e1")
    assert "可承诺：L = 11 分钟" in run("8.0000000000000001e1")
    assert 'name="threshold" value="8e1"' in run("8e1")

    # 撤下后历史保留当时输入的精确阈值
    html = run("80")
    assert "已撤下" in html and "阈值8e1" in html
    print("ok  阈值精确比较/科学计数法/表单与历史保留")


def test_threshold_rejects_bad_values():
    """NaN / 无穷 / 格式错误：报错，且当前结论与历史保持不变。"""
    import io as _io

    import app as web

    web.app.config.update(TESTING=True)
    c = web.app.test_client()
    rows = [f"{i},{50 + i}" for i in range(1, 11)]
    c.post("/upload",
           data={"file": (_io.BytesIO(("minute,score\n" + "\n".join(rows) + "\n").encode()),
                          "n.csv")},
           content_type="multipart/form-data")
    iv = "1-2\n5-6"
    c.post("/analyze", data={"threshold": "NaN-test", "U": "5", "K": "1",
                             "intervals": iv}, follow_redirects=True)  # 先制造一条历史
    c.post("/analyze", data={"threshold": "55", "U": "5", "K": "1",
                             "intervals": iv}, follow_redirects=True)
    cur_html = c.get("/").get_data(as_text=True)
    hist_before = cur_html.count("已撤下")

    for bad in ["nan", "NaN", "-inf", "Infinity", "abc", "8e", "", "0x10", "1,5"]:
        r = c.post("/analyze", data={"threshold": bad, "U": "5", "K": "1",
                                     "intervals": iv}, follow_redirects=True)
        html = r.get_data(as_text=True)
        assert "参数未通过校验" in html, bad
        assert "当前有效" in html, bad          # 当前结论仍在
        assert html.count("已撤下") == hist_before, bad  # 历史未增加
        assert f'name="threshold" value="{bad}"' in html, bad  # 回填本次输入
    print("ok  NaN/无穷/格式错误被拒且保留结论与历史")


def test_big_integer_scores():
    """整批仅两档相邻的有符号 64 位大整数：页面可打开，折线分出高低，刻度可读。"""
    import io as _io
    import re

    import app as web

    web.app.config.update(TESTING=True)
    c = web.app.test_client()
    lo, hi = -(2 ** 63), 2 ** 63 - 1
    rows = [f"{i},{hi if i % 2 else hi - 1}" for i in range(1, 11)]
    c.post("/upload",
           data={"file": (_io.BytesIO(("minute,score\n" + "\n".join(rows) + "\n").encode()),
                          "big.csv")},
           content_type="multipart/form-data")
    r = c.post("/analyze", data={"threshold": str(hi), "U": "10", "K": "1",
                                 "intervals": "1-10"}, follow_redirects=True)
    assert r.status_code == 200
    html = c.get("/").get_data(as_text=True)
    assert "可承诺" in html or "无法承诺" in html
    ys = {p.split(",")[1] for p in
          re.search(r'<polyline points="([^"]+)"', html).group(1).split()}
    assert len(ys) == 2, ys  # 相邻两档分到不同高度
    labels = re.findall(r'text-anchor="end" fill="#888">([^<]+)</text>', html)
    assert str(hi) in labels and str(hi - 1) in labels, labels
    # 回放数据以字符串下发，避免 JS Number 精度丢失
    replay = re.search(r'id="replay-data">(.*?)</script>', html, re.S).group(1)
    assert f'"{hi}"' in replay and f'"{hi - 1}"' in replay

    # 跨度拉到整个 64 位范围（含最小值）仍可打开
    rows = [f"{i},{hi if i % 2 else lo}" for i in range(1, 11)]
    c.post("/upload",
           data={"file": (_io.BytesIO(("minute,score\n" + "\n".join(rows) + "\n").encode()),
                          "wide.csv")},
           content_type="multipart/form-data")
    r = c.post("/analyze", data={"threshold": "0", "U": "10", "K": "1",
                                 "intervals": "1-10"}, follow_redirects=True)
    assert r.status_code == 200 and "参数未通过校验" not in r.get_data(as_text=True)
    assert c.get("/").status_code == 200
    print("ok  有符号 64 位大整数分值：图表/回放/刻度")


def main():
    test_compute_alerts()
    rng = random.Random(20261124)
    test_max_matching_vs_brute(rng)
    test_min_hits_vs_brute(rng)
    test_solve_vs_linear(rng)
    test_monotonicity(rng)
    test_edge_cases()
    test_web_app()
    test_threshold_precision_web()
    test_threshold_rejects_bad_values()
    test_big_integer_scores()
    print("\n全部自测通过。")


if __name__ == "__main__":
    main()
