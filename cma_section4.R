# Causal Multiverse Analysis using confounding equivalence -- Section 4.
# Reproduces the paper's Tables 1-4 (CSV) and Figures 1-4, A1 (PNG).
# Packages: dagitty, ggplot2, patchwork, diptest, mvtnorm. R >= 4.3.

library(dagitty)
library(ggplot2)
library(patchwork)
library(diptest)
library(mvtnorm)

RNGkind("Mersenne-Twister", "Inversion", "Rejection")
set.seed(1234)

n_boot <- 100000
n_dip  <- 10000

output_dir <- file.path("submission_code", "results_section4_final")
figure_dir <- file.path(output_dir, "figures")
dir.create(figure_dir, recursive = TRUE, showWarnings = FALSE)
theme_set(theme_bw(base_size = 12))

all_cov <- c("AE", "ASE", "CON", "ER", "FT", "GM", "LTA", "MAP", "PAP", "PAV")
cov_pos <- setNames(seq_along(all_cov) + 2L, all_cov)   # column of each covariate in P


# ---- Data -----------------------------------------------------------------

var_map <- c(
  LTG = "long_term_goal_grit",      AC  = "academic_achievement",
  CON = "conscientiousness",        GM  = "growth_mindset",
  FT  = "future_time_perspective",  LTA = "long_term_goal_awareness",
  MAP = "mastery_approach",         PAP = "performance_approach",
  PAV = "performance_avoidance",    ASE = "academic_self_efficacy",
  ER  = "effort_regulation",        AE  = "academic_engagement"
)

raw_data <- read.csv("submission_data.csv", check.names = FALSE)
analysis_data <- setNames(raw_data[, var_map], names(var_map))
analysis_data[] <- lapply(analysis_data, as.numeric)
analysis_data <- analysis_data[complete.cases(analysis_data), ]
analysis_data_z <- as.data.frame(scale(analysis_data))


# ---- Helpers --------------------------------------------------------------

set_code <- function(s) if (length(s) == 0) "none" else paste(s, collapse = "_")

# Enumerate the admissible adjustment sets for a DAG, then fit the standardized
# LTG coefficient (with 95% CI) for each. Returns the sets and a results table.
multiverse <- function(dag) {
  sets <- adjustmentSets(dag, exposure = "LTG", outcome = "AC",
                         effect = "total", type = "all")
  sets <- lapply(sets, function(s) sort(as.character(s)))
  sets <- sets[order(lengths(sets), vapply(sets, set_code, ""))]

  ind <- data.frame(set_id = seq_along(sets),
                    adjustment_set_code = vapply(sets, set_code, ""),
                    n_covariates = lengths(sets))
  for (cv in all_cov)
    ind[[paste0("has_", cv)]] <- as.integer(vapply(sets, function(s) cv %in% s, logical(1)))

  fits <- do.call(rbind, lapply(sets, function(vars) {
    fit <- lm(reformulate(c("LTG", vars), "AC"), analysis_data_z[, c("AC", "LTG", vars)])
    cf  <- summary(fit)$coefficients["LTG", ]; ci <- confint(fit, "LTG")
    data.frame(beta_std = cf[["Estimate"]], se_std = cf[["Std. Error"]],
               ci_std_low = ci[1], ci_std_high = ci[2])
  }))
  list(sets = sets, results = cbind(ind, fits))
}

# k-means labels used only to shade the multiverse figures.
cluster_layer <- function(b) {
  km  <- kmeans(b, centers = 2, nstart = 50)
  low <- which.min(tapply(b, km$cluster, mean))
  factor(ifelse(km$cluster == low, "low", "high"), levels = c("low", "high"))
}

make_positive_definite <- function(S, tol = 1e-8) {
  S <- (S + t(S)) / 2
  e <- eigen(S, symmetric = TRUE)
  e$values[e$values < tol] <- tol
  S <- e$vectors %*% diag(e$values) %*% t(e$vectors)
  S <- (S + t(S)) / 2
  diag(S) <- pmax(diag(S), tol)
  S
}

# GLS pooling of the dependent per-set estimates y through covariance V.
pool_gls <- function(y, V) {
  one  <- matrix(1, length(y), 1)
  Vi   <- solve(V)
  prec <- as.numeric(t(one) %*% Vi %*% one)
  pooled <- as.numeric((t(one) %*% Vi %*% y) / prec)
  se   <- sqrt(1 / prec)
  resid <- y - pooled
  Q  <- as.numeric(t(resid) %*% Vi %*% resid)
  df <- length(y) - 1
  data.frame(pooled_beta = pooled, pooled_se = se,
             Q = Q, Q_df = df, Q_p = pchisq(Q, df, lower.tail = FALSE),
             I2 = max(0, (Q - df) / Q))
}

gls_meta <- function(y, V, X) {
  Vi    <- solve(V)
  cov_b <- solve(t(X) %*% Vi %*% X)
  beta  <- as.numeric(cov_b %*% t(X) %*% Vi %*% y)
  se    <- sqrt(diag(cov_b))
  data.frame(term = colnames(X), estimate = beta, se = se,
             p = 2 * pnorm(-abs(beta / se)))
}

# Standardized LTG coefficient for every set on one resample. Each set is a
# subset of the same predictors, so its normal equations are a submatrix of
# one 12x12 cross-product -- a small solve() per set instead of 249 lm() fits.
spec_betas <- function(boot_data, sets) {
  Z <- scale(as.matrix(boot_data[, c("AC", "LTG", all_cov)]))
  if (anyNA(Z)) return(rep(NA_real_, length(sets)))
  P   <- cbind(1, Z[, c("LTG", all_cov)])
  XtX <- crossprod(P); Xty <- crossprod(P, Z[, "AC"])
  vapply(sets, function(s) {
    cols <- c(1L, 2L, cov_pos[s])
    tryCatch(solve(XtX[cols, cols], Xty[cols, ])[2L], error = function(e) NA_real_)
  }, numeric(1))
}

# As above with an added LTG x LTA column. With LTA centered in the resample
# the +1 SD g-computation ATE equals the LTG coefficient.
spec_ate_interaction <- function(boot_data, sets) {
  Z <- scale(as.matrix(boot_data[, c("AC", "LTG", all_cov)]))
  if (anyNA(Z)) return(rep(NA_real_, length(sets)))
  P   <- cbind(1, Z[, c("LTG", all_cov)], Z[, "LTG"] * Z[, "LTA"])
  XtX <- crossprod(P); Xty <- crossprod(P, Z[, "AC"])
  vapply(sets, function(s) {
    cols <- c(1L, 2L, cov_pos[s], ncol(P))
    tryCatch(solve(XtX[cols, cols], Xty[cols, ])[2L], error = function(e) NA_real_)
  }, numeric(1))
}

# Bootstrap the between-specification covariance (reseeded so every call is
# reproducible regardless of order).
bootstrap_cov <- function(sets, beta_fn) {
  set.seed(1234)
  mat <- matrix(NA_real_, n_boot, length(sets))
  for (i in seq_len(n_boot)) {
    idx <- sample.int(nrow(analysis_data), replace = TRUE)
    mat[i, ] <- beta_fn(analysis_data[idx, , drop = FALSE], sets)
  }
  make_positive_definite(cov(mat[complete.cases(mat), , drop = FALSE]))
}

# Dependence-aware dip p-value: simulate unimodal draws centered at the pool.
dip_pvalue <- function(D_obs, center, V) {
  set.seed(1234)
  null <- replicate(n_dip,
                    dip.test(as.numeric(rmvnorm(1, rep(center, nrow(V)), V)))$statistic)
  mean(null >= D_obs)
}


# ---- Original DAG (Figure 1) ----------------------------------------------

dag_original <- dagitty("
dag {
  LTG -> FT   GM -> LTG   MAP -> GM   LTA -> LTG   CON -> FT
  ASE -> PAP  ASE -> MAP  ASE -> GM   ASE -> CON   ASE -> AC
  PAV -> PAP  MAP -> PAV  ER -> GM    ER -> MAP    ER -> FT
  AE -> ER    AE -> LTA   AE -> CON   AE -> ASE    PAP -> FT   FT -> AC
}")

orig <- multiverse(dag_original)
adjustment_list <- orig$sets
spec_results    <- orig$results

b      <- spec_results$beta_std
ci_w   <- spec_results$ci_std_high - spec_results$ci_std_low
ci_sig <- spec_results$ci_std_low > 0 | spec_results$ci_std_high < 0
spec_results$layer <- cluster_layer(b)

# Table 1: descriptive summary of the c-equivalent multiverse.
table1 <- data.frame(
  quantity = c("Analytic sample (N)", "Valid adjustment sets (k)", "Set size range",
               "Mean b", "Median b", "SD of b", "Range of b",
               "95% CI excludes zero", "Median 95% CI width"),
  value = c(nrow(analysis_data), length(b),
            sprintf("%d-%d", min(lengths(adjustment_list)), max(lengths(adjustment_list))),
            sprintf("%.3f", mean(b)), sprintf("%.3f", median(b)), sprintf("%.3f", sd(b)),
            sprintf("[%.3f, %.3f]", min(b), max(b)),
            sprintf("%d/%d (%.1f%%)", sum(ci_sig), length(b), 100 * mean(ci_sig)),
            sprintf("%.3f", median(ci_w))))
print(table1, row.names = FALSE)
write.csv(table1, file.path(output_dir, "table1_descriptive.csv"), row.names = FALSE)

# Table 3: stratify by LTA inclusion.
table3 <- do.call(rbind, lapply(
  split(b, factor(spec_results$has_LTA, c(1, 0), c("LTA included", "LTA excluded"))),
  function(x) data.frame(k = length(x), mean = round(mean(x), 3), sd = round(sd(x), 3),
                         min = round(min(x), 3), max = round(max(x), 3))))
table3 <- cbind(stratum = rownames(table3), table3); rownames(table3) <- NULL
print(table3, row.names = FALSE)
write.csv(table3, file.path(output_dir, "table3_lta_strata.csv"), row.names = FALSE)

# Heterogeneity diagnostics.
dip_std <- dip.test(b)
w_iid   <- 1 / spec_results$se_std^2
Q_iid   <- sum(w_iid * (b - sum(w_iid * b) / sum(w_iid))^2)
df_iid  <- length(b) - 1

cov_pd     <- bootstrap_cov(adjustment_list, spec_betas)
pooled_dep <- pool_gls(b, cov_pd)
dip_p_dep  <- dip_pvalue(dip_std$statistic, pooled_dep$pooled_beta, cov_pd)

cat(sprintf("Original DAG (k = %d): Q_dep = %.2f (df = %d, p = %.3g), I2 = %.0f%%; Q_indep = %.2f (p = %.3g), I2 = %.0f%%\n",
            length(b), pooled_dep$Q, pooled_dep$Q_df, pooled_dep$Q_p, 100 * pooled_dep$I2,
            Q_iid, pchisq(Q_iid, df_iid, lower.tail = FALSE), max(0, (Q_iid - df_iid) / Q_iid) * 100))
cat(sprintf("  dip D = %.4f (p_dep = %.3g, p_indep = %.3g); cluster within-SD ~ %.3f, centers separated ~ %.3f\n",
            dip_std$statistic, dip_p_dep, dip_std$p.value,
            mean(tapply(b, spec_results$layer, sd)), abs(diff(tapply(b, spec_results$layer, mean)))))
cat(sprintf("  GLS pooled b = %.3f (SE = %.3f)\n", pooled_dep$pooled_beta, pooled_dep$pooled_se))


# ---- Meta-regression (Table 2) --------------------------------------------

# has_FT never varies (FT is structurally inadmissible) and is dropped.
indicators <- paste0("has_", all_cov)
indicators <- indicators[vapply(indicators,
                                function(v) length(unique(spec_results[[v]])) > 1, logical(1))]

meta_uni <- do.call(rbind, lapply(c(indicators, "n_covariates"), function(term) {
  out <- gls_meta(b, cov_pd, model.matrix(reformulate(term), spec_results))
  out[out$term != "(Intercept)", ]
}))

# n_covariates is the sum of the indicators, so drop one (has_AE) in the
# adjusted model to break the exact collinearity.
X_multi <- model.matrix(reformulate(c(setdiff(indicators, "has_AE"), "n_covariates")), spec_results)
meta_multi <- gls_meta(b, cov_pd, X_multi)
intercept  <- meta_multi[meta_multi$term == "(Intercept)", ]
cat(sprintf("Adjusted-model intercept: %.3f (SE = %.3f, p = %.3f)\n",
            intercept$estimate, intercept$se, intercept$p))

terms_order <- c(paste0("has_", sort(all_cov)), "n_covariates")
terms_order <- terms_order[terms_order %in% c(meta_uni$term, meta_multi$term)]
table2 <- data.frame(
  term     = terms_order,
  unadj_m  = meta_uni$estimate[match(terms_order, meta_uni$term)],
  unadj_se = meta_uni$se      [match(terms_order, meta_uni$term)],
  unadj_p  = meta_uni$p       [match(terms_order, meta_uni$term)],
  adj_m    = meta_multi$estimate[match(terms_order, meta_multi$term)],
  adj_se   = meta_multi$se      [match(terms_order, meta_multi$term)],
  adj_p    = meta_multi$p       [match(terms_order, meta_multi$term)])
write.csv(table2, file.path(output_dir, "table2_meta_regression.csv"), row.names = FALSE)


# ---- Modified DAG: LTA -> AC (Figure A1) ----------------------------------

dag_modified <- dagitty("
dag {
  LTG -> FT   GM -> LTG   MAP -> GM   LTA -> LTG   LTA -> AC   CON -> FT
  ASE -> PAP  ASE -> MAP  ASE -> GM   ASE -> CON   ASE -> AC
  PAV -> PAP  MAP -> PAV  ER -> GM    ER -> MAP    ER -> FT
  AE -> ER    AE -> LTA   AE -> CON   AE -> ASE    PAP -> FT   FT -> AC
}")

mod <- multiverse(dag_modified)
adjustment_list_mod <- mod$sets
spec_results_mod    <- mod$results
b_mod   <- spec_results_mod$beta_std
dip_mod <- dip.test(b_mod)

cov_pd_mod    <- bootstrap_cov(adjustment_list_mod, spec_betas)
pooled_mod    <- pool_gls(b_mod, cov_pd_mod)
dip_p_dep_mod <- dip_pvalue(dip_mod$statistic, pooled_mod$pooled_beta, cov_pd_mod)
cat(sprintf("Modified DAG (k = %d): mean = %.3f, SD = %.3f; GLS b = %.3f (SE = %.3f); dip D = %.4f (p_dep = %.3g, p_indep = %.3g)\n",
            length(b_mod), mean(b_mod), sd(b_mod), pooled_mod$pooled_beta, pooled_mod$pooled_se,
            dip_mod$statistic, dip_p_dep_mod, dip_mod$p.value))


# ---- LTG x LTA interaction ------------------------------------------------

# Refit each LTA-inclusive spec with the interaction; the +1 SD g-computation
# ATE is obtained by predicted-value differencing on the z-scored sample.
lta_sets <- adjustment_list[vapply(adjustment_list, function(s) "LTA" %in% s, logical(1))]
int_df <- do.call(rbind, lapply(lta_sets, function(vars) {
  z   <- as.data.frame(scale(analysis_data[, c("AC", "LTG", vars)]))
  fit <- lm(reformulate(c("LTG", vars, "LTG:LTA"), "AC"), data = z)
  z1  <- z; z1$LTG <- z1$LTG + 1
  cf  <- summary(fit)$coefficients["LTG:LTA", ]
  data.frame(ate_int = mean(predict(fit, z1) - predict(fit, z)),
             gamma_j = cf[["Estimate"]], p_g = cf[["Pr(>|t|)"]])
}))
dip_int <- dip.test(int_df$ate_int)

cov_pd_int    <- bootstrap_cov(lta_sets, spec_ate_interaction)
pooled_int    <- pool_gls(int_df$ate_int, cov_pd_int)
dip_p_dep_int <- dip_pvalue(dip_int$statistic, pooled_int$pooled_beta, cov_pd_int)
cat(sprintf("Interaction: gamma_bar = %.3f, range [%.3f, %.3f], max p = %.3f\n",
            mean(int_df$gamma_j), min(int_df$gamma_j), max(int_df$gamma_j), max(int_df$p_g)))
cat(sprintf("  mean ATE = %.3f; GLS ATE = %.3f (SE = %.3f); dip D = %.4f (p_dep = %.3g, p_indep = %.3g)\n",
            mean(int_df$ate_int), pooled_int$pooled_beta, pooled_int$pooled_se,
            dip_int$statistic, dip_p_dep_int, dip_int$p.value))


# ---- Cascade summary (Table 4) --------------------------------------------

table4 <- data.frame(
  stage  = c("Original DAG", "Modified DAG (LTA \u2192 AC)", "Modified DAG & (LTG \u00d7 LTA)"),
  k      = c(length(b), length(b_mod), nrow(int_df)),
  mean_b = c(mean(b), mean(b_mod), mean(int_df$ate_int)),
  sd_b   = c(sd(b), sd(b_mod), sd(int_df$ate_int)),
  dip_D  = c(dip_std$statistic, dip_mod$statistic, dip_int$statistic),
  dip_p  = c(dip_p_dep, dip_p_dep_mod, dip_p_dep_int),
  gls_b  = c(pooled_dep$pooled_beta, pooled_mod$pooled_beta, pooled_int$pooled_beta),
  gls_se = c(pooled_dep$pooled_se, pooled_mod$pooled_se, pooled_int$pooled_se))
print(table4, row.names = FALSE, digits = 3)
write.csv(table4, file.path(output_dir, "table4_cascade.csv"), row.names = FALSE)


# ---- Multiverse figures (Figures 2, 3, 4) ---------------------------------

xlab_b     <- expression("Standardized regression coefficient (" * italic(b) * ")")
xlim_bar   <- c(0.08, 0.21)
bw         <- diff(xlim_bar) / 30
xlim_panel <- c(-0.015, 0.325)
x_breaks   <- seq(0, 0.325, by = 0.05)
gls_text   <- function(v) sprintf("atop('GLS pooled', italic(b) == %.3f)", v)
legend_theme <- theme(legend.position = "right",
                      legend.text = element_text(size = 14),
                      legend.title = element_text(size = 15),
                      legend.key.size = unit(0.6, "cm"))

# Forest panel (estimates + CIs) over a histogram, shaded by cluster.
plot_multiverse <- function(spec, gls, legend_name, labs, gls_dx, gls_hjust) {
  cols <- c(low = "grey70", high = "grey25"); shp <- c(low = 16, high = 17)
  ord  <- spec[order(spec$beta_std), ]; ord$rank <- seq_len(nrow(ord))

  forest <- ggplot(ord, aes(beta_std, rank, colour = layer, fill = layer, shape = layer)) +
    geom_segment(aes(x = ci_std_low, xend = ci_std_high, yend = rank), alpha = 0.6, linewidth = 0.4) +
    geom_point(size = 1.2) +
    geom_line(aes(group = layer), linewidth = 0.6) +
    geom_vline(xintercept = 0, linetype = "dashed", colour = "grey50") +
    geom_vline(xintercept = gls, colour = "black") +
    annotate("text", x = 0.01, y = nrow(ord) * 0.60, label = "italic(b) == 0",
             hjust = 0, size = 3, colour = "grey40", parse = TRUE) +
    annotate("text", x = gls + gls_dx, y = nrow(ord) * 0.95, label = gls_text(gls),
             hjust = gls_hjust, size = 3.5, parse = TRUE) +
    scale_colour_manual(legend_name, values = cols, labels = labs) +
    scale_fill_manual(legend_name, values = cols, labels = labs) +
    scale_shape_manual(legend_name, values = shp, labels = labs) +
    scale_x_continuous(breaks = x_breaks) +
    scale_y_continuous(expand = expansion(mult = c(0, 0.02))) +
    coord_cartesian(xlim = xlim_panel, expand = FALSE) +
    labs(x = xlab_b, y = "Admissible adjustment set (ordered)") + legend_theme

  ymax <- ceiling(max(hist(spec$beta_std, breaks = seq(xlim_bar[1], xlim_bar[2], bw),
                           plot = FALSE)$counts) / 5) * 5
  histp <- ggplot(spec, aes(beta_std, fill = layer)) +
    geom_histogram(binwidth = bw, boundary = xlim_bar[1], alpha = 0.9,
                   position = "identity", colour = "black", linewidth = 0.2) +
    geom_vline(xintercept = gls, colour = "black", linewidth = 0.7) +
    annotate("text", x = gls - 0.002, y = ymax * 0.92, label = gls_text(gls),
             hjust = 1, size = 3, parse = TRUE) +
    scale_fill_manual(legend_name, values = cols, labels = labs) +
    scale_x_continuous(breaks = x_breaks) +
    scale_y_continuous(limits = c(0, ymax), expand = c(0, 0)) +
    coord_cartesian(xlim = xlim_panel, expand = FALSE) +
    labs(x = xlab_b, y = "Count") + legend_theme

  forest / histp
}

# Figure 2: original DAG.
ggsave(file.path(figure_dir, "fig2_multiverse.png"),
       plot_multiverse(spec_results, pooled_dep$pooled_beta, "Cluster",
                       c(low = "Lower-effect cluster", high = "Higher-effect cluster"),
                       gls_dx = 0.01, gls_hjust = 0),
       width = 9, height = 10, dpi = 300)

# Figure 3: modified DAG.
spec_results_mod$layer <- cluster_layer(b_mod)
ggsave(file.path(figure_dir, "fig3_multiverse_modified.png"),
       plot_multiverse(spec_results_mod, pooled_mod$pooled_beta, "Sub-mode",
                       c(low = "Lower sub-mode", high = "Upper sub-mode"),
                       gls_dx = -0.006, gls_hjust = 1),
       width = 9, height = 10, dpi = 300)

# Figure 4: additive vs interaction ATE distributions.
int_long <- rbind(data.frame(beta = b_mod, model = "Additive model"),
                  data.frame(beta = int_df$ate_int, model = "Interaction model"))
int_long$model <- factor(int_long$model, c("Additive model", "Interaction model"))

p_int <- ggplot(int_long, aes(beta)) +
  geom_histogram(data = subset(int_long, model == "Additive model"), aes(fill = model),
                 binwidth = bw, boundary = xlim_bar[1], alpha = 0.6,
                 position = "identity", colour = "grey40", linewidth = 0.3) +
  geom_histogram(data = subset(int_long, model == "Interaction model"), aes(fill = model),
                 binwidth = bw, boundary = xlim_bar[1], alpha = 0.6,
                 position = "identity", colour = "black", linewidth = 0.4) +
  geom_vline(xintercept = pooled_mod$pooled_beta, colour = "black", linewidth = 0.8) +
  geom_vline(xintercept = pooled_int$pooled_beta, linetype = "longdash",
             colour = "black", linewidth = 0.8) +
  annotate("text", x = pooled_mod$pooled_beta - 0.002, y = 33,
           label = sprintf("paste('GLS ', italic(b), ' = %.3f')", pooled_mod$pooled_beta),
           hjust = 1, size = 3, parse = TRUE) +
  annotate("text", x = pooled_int$pooled_beta + 0.002, y = 29,
           label = sprintf("paste('GLS ', italic(b), ' = %.3f')", pooled_int$pooled_beta),
           hjust = 0, size = 3, parse = TRUE) +
  scale_fill_manual(NULL, values = c("Additive model" = "grey75", "Interaction model" = "grey35")) +
  scale_x_continuous(breaks = x_breaks, expand = c(0, 0)) +
  scale_y_continuous(limits = c(0, 35), expand = c(0, 0)) +
  coord_cartesian(xlim = xlim_panel, expand = FALSE) +
  labs(x = xlab_b, y = "Count", title = "Interaction diagnostics",
       subtitle = "g-computation ATE of a +1 SD shift in LTG") + legend_theme
ggsave(file.path(figure_dir, "fig4_interaction.png"), p_int, width = 9, height = 5, dpi = 300)


# ---- DAG figures (Figure 1 and Figure A1) ---------------------------------

dag_nodes <- data.frame(
  name  = c("AE", "LTA", "GM", "LTG", "PAP", "PAV", "MAP", "ER", "FT", "AC", "CON", "ASE"),
  angle = c(90, 60, 30, 0, -30, -60, -90, -120, -150, 180, 150, 120))
dag_nodes$x <- cos(dag_nodes$angle * pi / 180)
dag_nodes$y <- sin(dag_nodes$angle * pi / 180)
dag_nodes$role <- factor(
  ifelse(dag_nodes$name == "LTG", "Treatment (LTG)",
         ifelse(dag_nodes$name == "AC", "Outcome (AC)", "Candidate covariates")),
  levels = c("Treatment (LTG)", "Outcome (AC)", "Candidate covariates"))

edges_original <- data.frame(
  from = c("LTG","GM","MAP","LTA","CON","ASE","ASE","ASE","ASE","ASE","PAV",
           "MAP","ER","ER","ER","AE","AE","AE","AE","PAP","FT"),
  to   = c("FT","LTG","GM","LTG","FT","PAP","MAP","GM","CON","AC","PAP",
           "PAV","GM","MAP","FT","ER","LTA","CON","ASE","FT","AC"))
edges_modified <- rbind(edges_original, data.frame(from = "LTA", to = "AC"))

# Pull arrowheads back so they stop outside the node markers.
shrink_edge <- function(df, r = 0.09) {
  if (nrow(df) == 0L) return(df)
  dx <- df$xend - df$x; dy <- df$yend - df$y; d <- sqrt(dx^2 + dy^2)
  df$x <- df$x + dx / d * r; df$y <- df$y + dy / d * r
  df$xend <- df$xend - dx / d * r; df$yend <- df$yend - dy / d * r
  df
}

# Triangles render larger than squares/circles at equal size, so the outcome
# node gets a smaller value to match the visual area.
role_sizes <- c("Treatment (LTG)" = 13, "Outcome (AC)" = 10, "Candidate covariates" = 13)

build_dag_plot <- function(edges, title, highlight = NULL) {
  edges$x    <- dag_nodes$x[match(edges$from, dag_nodes$name)]
  edges$y    <- dag_nodes$y[match(edges$from, dag_nodes$name)]
  edges$xend <- dag_nodes$x[match(edges$to, dag_nodes$name)]
  edges$yend <- dag_nodes$y[match(edges$to, dag_nodes$name)]
  edges$hl <- if (is.null(highlight)) logical(nrow(edges))
  else edges$from == highlight[1] & edges$to == highlight[2]

  p <- ggplot() +
    geom_segment(data = shrink_edge(edges[!edges$hl, ]),
                 aes(x, y, xend = xend, yend = yend), colour = "grey50", linewidth = 0.35,
                 arrow = arrow(length = unit(0.018, "npc"), type = "closed"))
  if (any(edges$hl)) {
    hl <- shrink_edge(edges[edges$hl, ]); hl$lab <- "Added edge: LTA \u2192 AC"
    p <- p + geom_segment(data = hl, aes(x, y, xend = xend, yend = yend, colour = lab),
                          linewidth = 1.2, arrow = arrow(length = unit(0.024, "npc"), type = "closed")) +
      scale_colour_manual(NULL, values = c("Added edge: LTA \u2192 AC" = "black"))
  }
  p +
    geom_point(data = dag_nodes, aes(x, y, fill = role, shape = role, size = role),
               colour = "black", stroke = 0.5) +
    geom_text(data = dag_nodes, aes(x, y, label = name), size = 3.3, fontface = "bold") +
    scale_fill_manual(NULL, drop = FALSE,
                      values = c("Treatment (LTG)" = "white", "Outcome (AC)" = "grey55",
                                 "Candidate covariates" = "grey85")) +
    scale_shape_manual(NULL, drop = FALSE,
                       values = c("Treatment (LTG)" = 22, "Outcome (AC)" = 24, "Candidate covariates" = 21)) +
    scale_size_manual(values = role_sizes, guide = "none") +
    coord_equal(xlim = c(-1.25, 1.25), ylim = c(-1.25, 1.25), clip = "off") +
    labs(title = title) +
    guides(fill  = guide_legend(order = 1, nrow = 1, byrow = TRUE, override.aes = list(size = c(5, 4, 5))),
           shape = guide_legend(order = 1, nrow = 1, byrow = TRUE, override.aes = list(size = c(5, 4, 5))),
           colour = guide_legend(order = 2, nrow = 1, override.aes = list(linewidth = 1.2))) +
    theme_void(base_size = 12) +
    theme(plot.background = element_rect(fill = "white", colour = NA),
          plot.title = element_text(hjust = 0.5, size = 12, margin = margin(b = 6)),
          plot.margin = margin(6, 8, 10, 8),
          legend.position = "bottom", legend.box = "vertical", legend.box.just = "center",
          legend.margin = margin(t = 4, b = 0),
          legend.key.size = unit(0.8, "cm"), legend.text = element_text(size = 11))
}

ggsave(file.path(figure_dir, "fig1_dag.png"),
       build_dag_plot(edges_original, "Original DAG: causal structure assumed in the main analysis"),
       width = 6, height = 6.4, dpi = 300, bg = "white")
ggsave(file.path(figure_dir, "figA1_dag_modified.png"),
       build_dag_plot(edges_modified, "Modified DAG: LTA \u2192 AC added", highlight = c("LTA", "AC")),
       width = 6, height = 6.4, dpi = 300, bg = "white")

cat("\nDone. Outputs in:", output_dir, "\n")

