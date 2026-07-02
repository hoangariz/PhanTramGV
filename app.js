/**
 * Oxy Solver - Core Application Script
 * Built with vanilla ES6 Javascript
 */

// Color Palette for boundary lines
const BOUNDARY_COLORS = [
    '#6366f1', // Indigo
    '#10b981', // Emerald
    '#06b6d4', // Cyan
    '#f59e0b', // Amber
    '#d946ef', // Fuchsia
    '#f43f5e', // Rose
    '#3b82f6', // Blue
    '#84cc16'  // Lime
];

// Formats a number to Vietnamese standard: strips trailing zeros, uses commas for decimals
function formatNum(val, maxDecimals = 4) {
    if (val === null || val === undefined || isNaN(val)) return '';
    // Clean up tiny floating point errors like 0.0000000000000001 or 8.999999999999999
    const rounded = Math.round(val * 1e10) / 1e10;
    return rounded.toLocaleString('vi-VN', { maximumFractionDigits: maxDecimals });
}

// App State
const state = {
    constraints: [],
    zoom: 40,             // pixels per unit
    panOffset: { x: 0, y: 0 }, // camera translation
    isPanning: false,
    panStart: { x: 0, y: 0 },
    lpEnabled: false,
    lpObjective: { a: 3, b: 5, optType: 'max' },
    vertices: [],         // true mathematical vertices
    hoveredVertexIdx: null,
    canvasSize: { width: 0, height: 0 },
    mousePos: { x: 0, y: 0 } // current Cartesian mouse coordinates
};

// UI Elements
const els = {
    canvas: document.getElementById('graph-canvas'),
    inequalitiesList: document.getElementById('inequalities-list'),
    addIneqBtn: document.getElementById('add-ineq-btn'),
    lpToggle: document.getElementById('lp-toggle'),
    lpContainer: document.getElementById('lp-container'),
    lpA: document.getElementById('lp-a'),
    lpB: document.getElementById('lp-b'),
    lpOptTypes: document.getElementsByName('lp-opt'),
    verticesTableBody: document.getElementById('vertices-table-body'),
    noVerticesMsg: document.getElementById('no-vertices-msg'),
    zoomInBtn: document.getElementById('zoom-in-btn'),
    zoomOutBtn: document.getElementById('zoom-out-btn'),
    resetViewBtn: document.getElementById('reset-view-btn'),
    exportBtn: document.getElementById('export-btn'),
    coordBadge: document.getElementById('coord-badge'),
    emptyWarning: document.getElementById('empty-warning'),
    presetBtns: document.querySelectorAll('.preset-btn')
};

const ctx = els.canvas.getContext('2d');

// --- INEQUALITY PARSER ---
// Parses a string inequality like "3x + y <= 21" into coefficients a, b, c for "ax + by <= c"
class InequalityParser {
    static parse(str) {
        // Remove spaces and normalize operators
        let clean = str.replace(/\s+/g, '')
                       .replace(/−/g, '-')
                       .replace(/≤/g, '<=')
                       .replace(/≥/g, '>=');
        
        // Find comparison operator
        const opMatch = clean.match(/(<=|>=|<|>)/);
        if (!opMatch) {
            throw new Error("Thiếu ký tự so sánh (<=, >=, <, >)");
        }
        
        const operator = opMatch[0];
        const parts = clean.split(operator);
        if (parts.length !== 2) {
            throw new Error("Cú pháp không hợp lệ");
        }
        
        const lhs = parts[0];
        const rhsVal = parseFloat(parts[1]);
        if (isNaN(rhsVal)) {
            throw new Error("Vế phải phải là một số thực");
        }
        
        // Regex to parse LHS: matches coefficients with x or y, or standalone constants
        // Captures: 1: coeff string, 2: variable name, 3: constant term
        const termRegex = /([+-]?(?:\d*(?:\.\d+)?))?([xy])|([+-]?\d+(?:\.\d+)?)/g;
        
        let match;
        let coefX = 0;
        let coefY = 0;
        let constantOffset = 0;
        let hasVariables = false;
        
        while ((match = termRegex.exec(lhs)) !== null) {
            if (match[0] === '') {
                termRegex.lastIndex++;
                continue;
            }
            
            const coeffStr = match[1];
            const variable = match[2];
            const constantStr = match[3];
            
            if (variable) {
                hasVariables = true;
                let val = 1;
                if (coeffStr === '+') val = 1;
                else if (coeffStr === '-') val = -1;
                else if (coeffStr && coeffStr !== '') val = parseFloat(coeffStr);
                
                if (variable === 'x') coefX += val;
                else if (variable === 'y') coefY += val;
            } else if (constantStr) {
                constantOffset += parseFloat(constantStr);
            }
        }
        
        if (!hasVariables) {
            throw new Error("Phương trình không chứa ẩn x hoặc y");
        }
        
        // Equation: coefX*x + coefY*y + constantOffset [operator] rhsVal
        // Normalize: coefX*x + coefY*y [operator] rhsVal - constantOffset
        let finalC = rhsVal - constantOffset;
        let finalA = coefX;
        let finalB = coefY;
        let finalOp = operator;
        
        // Standardize to <= or < form
        if (operator === '>=' || operator === '>') {
            finalA = -finalA;
            finalB = -finalB;
            finalC = -finalC;
            finalOp = (operator === '>=') ? '<=' : '<';
        }
        
        return {
            a: finalA,
            b: finalB,
            c: finalC,
            operator: finalOp,
            isStrict: (finalOp === '<' || operator === '>')
        };
    }
}

// --- MATHEMATICAL CORE ENGINE ---

// Sutherland-Hodgman Polygon Clipper
// Clips a polygon (array of {x, y}) against a half-plane ax + by <= c
function clipPolygon(poly, a, b, c) {
    if (poly.length === 0) return [];
    
    const result = [];
    const epsilon = 1e-8;
    
    // Check if point is inside the half-plane (ax + by <= c)
    const isInside = (pt) => (a * pt.x + b * pt.y) <= (c + epsilon);
    
    // Find intersection of edge (p1, p2) with boundary line ax + by = c
    const intersect = (p1, p2) => {
        const d1 = a * p1.x + b * p1.y - c;
        const d2 = a * p2.x + b * p2.y - c;
        const t = d1 / (d1 - d2);
        return {
            x: p1.x + t * (p2.x - p1.x),
            y: p1.y + t * (p2.y - p1.y)
        };
    };
    
    let prev = poly[poly.length - 1];
    let prevInside = isInside(prev);
    
    for (let i = 0; i < poly.length; i++) {
        const curr = poly[i];
        const currInside = isInside(curr);
        
        if (currInside) {
            if (!prevInside) {
                result.push(intersect(prev, curr));
            }
            result.push(curr);
        } else if (prevInside) {
            result.push(intersect(prev, curr));
        }
        
        prev = curr;
        prevInside = currInside;
    }
    
    return result;
}

// Get intersection of two lines: a1*x + b1*y = c1 and a2*x + b2*y = c2
function intersectLines(l1, l2) {
    const D = l1.a * l2.b - l2.a * l1.b;
    if (Math.abs(D) < 1e-9) return null; // Parallel lines
    
    const Dx = l1.c * l2.b - l2.c * l1.b;
    const Dy = l1.a * l2.c - l2.a * l1.c;
    
    return {
        x: Dx / D,
        y: Dy / D
    };
}

// Calculate the vertices of the feasible region (all intersection points that satisfy all constraints)
function calculateVertices() {
    const validVertices = [];
    const constraints = state.constraints.filter(c => !c.error && c.active);
    
    if (constraints.length === 0) {
        state.vertices = [];
        return;
    }
    
    const epsilon = 1e-5; // Tolerance for checking inequalities
    
    // Intersect all pairs of constraints
    for (let i = 0; i < constraints.length; i++) {
        for (let j = i + 1; j < constraints.length; j++) {
            const pt = intersectLines(constraints[i], constraints[j]);
            if (!pt) continue;
            
            // Check if this point satisfies ALL active constraints
            let satisfiesAll = true;
            for (const c of constraints) {
                const val = c.a * pt.x + c.b * pt.y;
                if (val > c.c + epsilon) {
                    satisfiesAll = false;
                    break;
                }
            }
            
            if (satisfiesAll) {
                // Deduplicate: check if this point is already in the list
                const isDuplicate = validVertices.some(v => 
                    Math.abs(v.x - pt.x) < epsilon && Math.abs(v.y - pt.y) < epsilon
                );
                if (!isDuplicate) {
                    validVertices.push(pt);
                }
            }
        }
    }
    
    // Sort vertices counter-clockwise around their centroid
    if (validVertices.length > 2) {
        const centroid = validVertices.reduce((acc, v) => ({ x: acc.x + v.x, y: acc.y + v.y }), { x: 0, y: 0 });
        centroid.x /= validVertices.length;
        centroid.y /= validVertices.length;
        
        validVertices.sort((p1, p2) => {
            const a1 = Math.atan2(p1.y - centroid.y, p1.x - centroid.x);
            const a2 = Math.atan2(p2.y - centroid.y, p2.x - centroid.x);
            return a1 - a2;
        });
    }
    
    state.vertices = validVertices;
}

// --- COORDINATE TRANSLATIONS ---
function toScreenX(x) {
    return state.canvasSize.width / 2 + state.panOffset.x + x * state.zoom;
}

function toScreenY(y) {
    return state.canvasSize.height / 2 + state.panOffset.y - y * state.zoom;
}

function toCartesianX(sx) {
    return (sx - (state.canvasSize.width / 2 + state.panOffset.x)) / state.zoom;
}

function toCartesianY(sy) {
    return ((state.canvasSize.height / 2 + state.panOffset.y) - sy) / state.zoom;
}

// --- CANVAS RENDERING ENGINE ---

let hatchPattern = null;
function getHatchPattern() {
    if (hatchPattern) return hatchPattern;
    const pCanvas = document.createElement('canvas');
    pCanvas.width = 12;
    pCanvas.height = 12;
    const pCtx = pCanvas.getContext('2d');
    pCtx.strokeStyle = 'rgba(15, 23, 42, 0.18)'; // Bolder hatch color
    pCtx.lineWidth = 1.8; // Thicker line
    pCtx.beginPath();
    pCtx.moveTo(0, 12);
    pCtx.lineTo(12, 0);
    pCtx.stroke();
    hatchPattern = ctx.createPattern(pCanvas, 'repeat');
    return hatchPattern;
}

function fitViewToBounds(xMinTarget, xMaxTarget, yMinTarget, yMaxTarget) {
    const padding = 1.0;
    const targetW = xMaxTarget - xMinTarget + padding * 2;
    const targetH = yMaxTarget - yMinTarget + padding * 2;
    
    const w = state.canvasSize.width || els.canvas.width || 600;
    const h = state.canvasSize.height || els.canvas.height || 600;
    
    state.zoom = Math.min(w / targetW, h / targetH);
    state.zoom = Math.max(5, Math.min(1000, state.zoom));
    
    const xCenter = (xMinTarget + xMaxTarget) / 2;
    const yCenter = (yMinTarget + yMaxTarget) / 2;
    
    state.panOffset.x = -xCenter * state.zoom;
    state.panOffset.y = yCenter * state.zoom;
}

// Get intersection of a constraint boundary line with Ox and Oy axes
function getIntercepts(c) {
    const intercepts = { x: null, y: null };
    if (Math.abs(c.a) > 1e-9) {
        intercepts.x = { x: c.c / c.a, y: 0 };
    }
    if (Math.abs(c.b) > 1e-9) {
        intercepts.y = { x: 0, y: c.c / c.b };
    }
    return intercepts;
}

// Draw intercepts of constraint boundary lines on Ox and Oy axes
function drawIntercepts() {
    const activeConstraints = state.constraints.filter(c => !c.error && c.active);
    
    activeConstraints.forEach(c => {
        const intercepts = getIntercepts(c);
        
        ctx.textBaseline = 'middle';
        
        // 1. Intersect Ox (y = 0)
        if (intercepts.x) {
            const sx = toScreenX(intercepts.x.x);
            const sy = toScreenY(0);
            
            if (sx >= 0 && sx <= state.canvasSize.width) {
                // White fill, colored border (similar to vertices)
                ctx.fillStyle = '#ffffff';
                ctx.strokeStyle = c.color;
                ctx.lineWidth = 2.5;
                ctx.beginPath();
                ctx.arc(sx, sy, 5, 0, Math.PI * 2);
                ctx.fill();
                ctx.stroke();
                
                // Coordinate label
                ctx.fillStyle = '#475569';
                ctx.font = '600 11px Space Grotesk, sans-serif';
                ctx.textAlign = 'center';
                let labelY = sy + 15;
                if (labelY > state.canvasSize.height - 10) {
                    labelY = sy - 15;
                }
                ctx.fillText(`(${formatNum(intercepts.x.x)}; 0)`, sx, labelY);
            }
        }
        
        // 2. Intersect Oy (x = 0)
        if (intercepts.y) {
            const sx = toScreenX(0);
            const sy = toScreenY(intercepts.y.y);
            
            if (sy >= 0 && sy <= state.canvasSize.height) {
                // White fill, colored border (similar to vertices)
                ctx.fillStyle = '#ffffff';
                ctx.strokeStyle = c.color;
                ctx.lineWidth = 2.5;
                ctx.beginPath();
                ctx.arc(sx, sy, 5, 0, Math.PI * 2);
                ctx.fill();
                ctx.stroke();
                
                // Coordinate label
                ctx.fillStyle = '#475569';
                ctx.font = '600 11px Space Grotesk, sans-serif';
                ctx.textAlign = 'right';
                let labelX = sx - 8;
                if (labelX < 10) {
                    labelX = sx + 8;
                    ctx.textAlign = 'left';
                }
                ctx.fillText(`(0; ${formatNum(intercepts.y.y)})`, labelX, sy);
            }
        }
    });
}

function render() {
    // Resize canvas if needed
    const rect = els.canvas.getBoundingClientRect();
    if (els.canvas.width !== rect.width || els.canvas.height !== rect.height) {
        els.canvas.width = rect.width;
        els.canvas.height = rect.height;
        state.canvasSize.width = rect.width;
        state.canvasSize.height = rect.height;
    }
    
    const width = state.canvasSize.width;
    const height = state.canvasSize.height;
    
    // Auto initialize view bounds on first render
    if (!state.viewInitialized && width > 0 && height > 0) {
        fitViewToBounds(-1, 9, -1, 10);
        state.viewInitialized = true;
    }
    
    // 1. Clear Canvas with White background
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, width, height);
    
    // Get visible Cartesian boundaries
    const xMin = toCartesianX(0);
    const xMax = toCartesianX(width);
    const yMin = toCartesianY(height);
    const yMax = toCartesianY(0);
    
    // 2. Draw FEASIBLE REGION (Yellow) & NON-FEASIBLE REGION (Light Slate + Hatched)
    const activeConstraints = state.constraints.filter(c => !c.error && c.active);
    
    let feasiblePolygon = [
        { x: xMin, y: yMin },
        { x: xMax, y: yMin },
        { x: xMax, y: yMax },
        { x: xMin, y: yMax }
    ];
    
    for (const c of activeConstraints) {
        feasiblePolygon = clipPolygon(feasiblePolygon, c.a, c.b, c.c);
    }
    
    if (feasiblePolygon.length >= 3) {
        // Draw feasible region filled with yellow
        ctx.fillStyle = 'rgba(234, 179, 8, 0.95)'; // Yellow 500 at 95% opacity
        ctx.beginPath();
        ctx.moveTo(toScreenX(feasiblePolygon[0].x), toScreenY(feasiblePolygon[0].y));
        for (let i = 1; i < feasiblePolygon.length; i++) {
            ctx.lineTo(toScreenX(feasiblePolygon[i].x), toScreenY(feasiblePolygon[i].y));
        }
        ctx.closePath();
        ctx.fill();

        // Draw hatched lines on the non-feasible region
        ctx.save();
        ctx.beginPath();
        // Outer box covering entire canvas
        ctx.rect(0, 0, width, height);
        // Inner polygon (subtracted)
        ctx.moveTo(toScreenX(feasiblePolygon[0].x), toScreenY(feasiblePolygon[0].y));
        for (let i = 1; i < feasiblePolygon.length; i++) {
            ctx.lineTo(toScreenX(feasiblePolygon[i].x), toScreenY(feasiblePolygon[i].y));
        }
        ctx.closePath();
        ctx.clip('evenodd');

        // Fill non-feasible with a light slate background
        ctx.fillStyle = '#f8fafc';
        ctx.fillRect(0, 0, width, height);

        // Fill non-feasible with diagonal hatched lines
        ctx.fillStyle = getHatchPattern();
        ctx.fillRect(0, 0, width, height);
        ctx.restore();
        
        els.emptyWarning.classList.remove('visible');
    } else {
        // Feasible region is empty - fill the whole canvas with hatched lines
        ctx.fillStyle = '#f8fafc';
        ctx.fillRect(0, 0, width, height);
        ctx.fillStyle = getHatchPattern();
        ctx.fillRect(0, 0, width, height);
        
        if (activeConstraints.length > 0) {
            els.emptyWarning.classList.add('visible');
        } else {
            els.emptyWarning.classList.remove('visible');
        }
    }
    
    // 3. Draw GRID LINES & TICKS
    drawGrid(xMin, xMax, yMin, yMax);
    
    // 4. Draw AXES (Ox, Oy)
    drawAxes();
    
    // 5. Draw BOUNDARY LINES of Inequalities
    drawBoundaryLines(xMin, xMax, yMin, yMax);
    
    // 5.5 Draw Axis Intercept points
    drawIntercepts();
    
    // 6. Draw MATHEMATICAL VERTICES
    drawVertices();
    
    // 7. Draw TOOLTIPS / INTERACTIVE LABELS
    drawHoveredTooltip();
}

// Draws adaptive grid lines and labels
function drawGrid(xMin, xMax, yMin, yMax) {
    const minPixelStep = 45;
    const rawStep = minPixelStep / state.zoom;
    const magnitude = Math.pow(10, Math.floor(Math.log10(rawStep)));
    const normalized = rawStep / magnitude;
    
    let step;
    if (normalized < 1.5) step = 1 * magnitude;
    else if (normalized < 3.5) step = 2 * magnitude;
    else if (normalized < 7.5) step = 5 * magnitude;
    else step = 10 * magnitude;
    
    ctx.lineWidth = 1;
    ctx.font = '10px Space Grotesk, sans-serif';
    ctx.textBaseline = 'middle';
    
    // Vertical Grid Lines
    const startGridX = Math.ceil(xMin / step) * step;
    for (let x = startGridX; x <= xMax; x += step) {
        if (Math.abs(x) < 1e-9) continue; // Skip Oy axis (drawn separately)
        
        const sx = toScreenX(x);
        ctx.strokeStyle = 'rgba(15, 23, 42, 0.06)'; // Visible on white background
        ctx.beginPath();
        ctx.moveTo(sx, 0);
        ctx.lineTo(sx, state.canvasSize.height);
        ctx.stroke();
        
        // Draw coordinate labels along the grid lines
        ctx.fillStyle = '#64748b';
        ctx.textAlign = 'center';
        
        // Keep labels on screen, pinned to bottom or near axis
        let labelY = toScreenY(0) + 12;
        if (labelY < 15) labelY = 15;
        if (labelY > state.canvasSize.height - 15) labelY = state.canvasSize.height - 15;
        
        // Format decimal nicely
        ctx.fillText(formatNum(x), sx, labelY);
    }
    
    // Horizontal Grid Lines
    const startGridY = Math.ceil(yMin / step) * step;
    for (let y = startGridY; y <= yMax; y += step) {
        if (Math.abs(y) < 1e-9) continue; // Skip Ox axis
        
        const sy = toScreenY(y);
        ctx.strokeStyle = 'rgba(15, 23, 42, 0.06)';
        ctx.beginPath();
        ctx.moveTo(0, sy);
        ctx.lineTo(state.canvasSize.width, sy);
        ctx.stroke();
        
        ctx.fillStyle = '#64748b';
        ctx.textAlign = 'right';
        
        let labelX = toScreenX(0) - 8;
        if (labelX < 15) {
            labelX = 15;
            ctx.textAlign = 'left';
        }
        if (labelX > state.canvasSize.width - 15) {
            labelX = state.canvasSize.width - 15;
        }
        
        ctx.fillText(formatNum(y), labelX, sy);
    }
}

// Draws Ox, Oy axes and Origin
function drawAxes() {
    const ox = toScreenX(0);
    const oy = toScreenY(0);
    
    ctx.strokeStyle = '#334155';
    ctx.lineWidth = 1.5;
    ctx.fillStyle = '#334155';
    
    // Draw Ox Axis
    if (oy >= 0 && oy <= state.canvasSize.height) {
        ctx.beginPath();
        ctx.moveTo(0, oy);
        ctx.lineTo(state.canvasSize.width, oy);
        ctx.stroke();
        
        // Arrow & Label x
        ctx.beginPath();
        ctx.moveTo(state.canvasSize.width - 10, oy - 4);
        ctx.lineTo(state.canvasSize.width, oy);
        ctx.lineTo(state.canvasSize.width - 10, oy + 4);
        ctx.fill();
        
        ctx.font = '700 13px Space Grotesk, sans-serif';
        ctx.textAlign = 'right';
        ctx.fillText('x', state.canvasSize.width - 15, oy - 15);
    }
    
    // Draw Oy Axis
    if (ox >= 0 && ox <= state.canvasSize.width) {
        ctx.beginPath();
        ctx.moveTo(ox, 0);
        ctx.lineTo(ox, state.canvasSize.height);
        ctx.stroke();
        
        // Arrow & Label y
        ctx.beginPath();
        ctx.moveTo(ox - 4, 10);
        ctx.lineTo(ox, 0);
        ctx.lineTo(ox + 4, 10);
        ctx.fill();
        
        ctx.font = '700 13px Space Grotesk, sans-serif';
        ctx.textAlign = 'left';
        ctx.fillText('y', ox + 12, 15);
    }
    
    // Origin O Label
    if (ox >= 0 && ox <= state.canvasSize.width && oy >= 0 && oy <= state.canvasSize.height) {
        ctx.font = 'italic 12px Plus Jakarta Sans, sans-serif';
        ctx.textAlign = 'right';
        ctx.fillText('O', ox - 5, oy + 12);
    }
}

// Draws the boundary lines of all active inequalities
function drawBoundaryLines(xMin, xMax, yMin, yMax) {
    const activeConstraints = state.constraints.filter(c => !c.error && c.active);
    
    activeConstraints.forEach(c => {
        ctx.beginPath();
        ctx.strokeStyle = c.color;
        ctx.lineWidth = 2.5;
        
        // Configure strict dash style
        if (c.isStrict) {
            ctx.setLineDash([8, 6]);
        } else {
            ctx.setLineDash([]);
        }
        
        // Line equation: ax + by = c
        // If vertical line (b = 0)
        if (Math.abs(c.b) < 1e-9) {
            const x = c.c / c.a;
            const sx = toScreenX(x);
            ctx.moveTo(sx, 0);
            ctx.lineTo(sx, state.canvasSize.height);
        }
        // If horizontal line (a = 0)
        else if (Math.abs(c.a) < 1e-9) {
            const y = c.c / c.b;
            const sy = toScreenY(y);
            ctx.moveTo(0, sy);
            ctx.lineTo(state.canvasSize.width, sy);
        }
        // General line: y = (c - ax) / b
        else {
            const yLeft = (c.c - c.a * xMin) / c.b;
            const yRight = (c.c - c.a * xMax) / c.b;
            ctx.moveTo(0, toScreenY(yLeft));
            ctx.lineTo(state.canvasSize.width, toScreenY(yRight));
        }
        ctx.stroke();
    });
    ctx.setLineDash([]); // Reset dash state
}

// Draws active vertices on Ox/Oy graph
function drawVertices() {
    const showLP = state.lpEnabled;
    const optimalIdx = getOptimalVertexIndex();
    
    state.vertices.forEach((v, idx) => {
        const sx = toScreenX(v.x);
        const sy = toScreenY(v.y);
        
        const isHovered = (idx === state.hoveredVertexIdx);
        const isOptimal = (showLP && idx === optimalIdx);
        
        // Draw glow effect for optimal LP solution
        if (isOptimal) {
            ctx.fillStyle = 'rgba(16, 185, 129, 0.2)';
            ctx.beginPath();
            ctx.arc(sx, sy, 15 + Math.sin(Date.now() / 150) * 4, 0, Math.PI * 2);
            ctx.fill();
        }
        
        // Node border/fill
        if (isOptimal) {
            ctx.strokeStyle = '#059669';
            ctx.fillStyle = '#ffffff';
            ctx.lineWidth = 3;
        } else if (isHovered) {
            ctx.strokeStyle = '#4f46e5';
            ctx.fillStyle = '#ffffff';
            ctx.lineWidth = 3;
        } else {
            ctx.strokeStyle = '#334155';
            ctx.fillStyle = '#ffffff';
            ctx.lineWidth = 2;
        }
        
        ctx.beginPath();
        ctx.arc(sx, sy, isHovered ? 7 : 5, 0, Math.PI * 2);
        ctx.fill();
        ctx.stroke();
        
        // Label the node (A, B, C...)
        const label = String.fromCharCode(65 + idx); // A, B, C...
        ctx.fillStyle = isOptimal ? '#059669' : (isHovered ? '#4f46e5' : '#0f172a');
        ctx.font = '700 12px Space Grotesk, sans-serif';
        ctx.textAlign = 'left';
        ctx.fillText(` ${label}`, sx + 6, sy - 6);
    });
}

// Render dynamic tooltip for hovered vertex
function drawHoveredTooltip() {
    if (state.hoveredVertexIdx === null) return;
    const v = state.vertices[state.hoveredVertexIdx];
    if (!v) return;
    
    const sx = toScreenX(v.x);
    const sy = toScreenY(v.y);
    const label = String.fromCharCode(65 + state.hoveredVertexIdx);
    
    let text = `${label}(${formatNum(v.x)}; ${formatNum(v.y)})`;
    if (state.lpEnabled) {
        const val = state.lpObjective.a * v.x + state.lpObjective.b * v.y;
        text += `  ➔  F = ${formatNum(val)}`;
    }
    
    ctx.font = '600 12px Plus Jakarta Sans, sans-serif';
    const textWidth = ctx.measureText(text).width;
    
    const paddingX = 10;
    const paddingY = 6;
    const cardW = textWidth + paddingX * 2;
    const cardH = 24;
    
    const cardX = sx - cardW / 2;
    const cardY = sy - cardH - 18;
    
    // Draw tooltip box
    ctx.fillStyle = 'rgba(15, 23, 42, 0.9)';
    ctx.strokeStyle = 'rgba(255, 255, 255, 0.15)';
    ctx.lineWidth = 1;
    
    ctx.beginPath();
    ctx.roundRect(cardX, cardY, cardW, cardH, 6);
    ctx.fill();
    ctx.stroke();
    
    // Text inside box
    ctx.fillStyle = '#fff';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, sx, cardY + cardH / 2);
}

// --- STATE MANAGEMENT ---

// Evaluate optimal vertex based on objective function
function getOptimalVertexIndex() {
    if (state.vertices.length === 0) return -1;
    
    const { a, b, optType } = state.lpObjective;
    let optimalVal = optType === 'max' ? -Infinity : Infinity;
    let optimalIdx = -1;
    
    state.vertices.forEach((v, idx) => {
        const val = a * v.x + b * v.y;
        if (optType === 'max') {
            if (val > optimalVal) {
                optimalVal = val;
                optimalIdx = idx;
            }
        } else {
            if (val < optimalVal) {
                optimalVal = val;
                optimalIdx = idx;
            }
        }
    });
    
    return optimalIdx;
}

const SVG_EYE_OPEN = `
    <svg viewBox="0 0 24 24" width="16" height="16" stroke="currentColor" stroke-width="2.5" fill="none" stroke-linecap="round" stroke-linejoin="round">
        <path d="M1 12s4-8 11-8 11 8 11 8-4 8-11 8-11-8-11-8z"></path>
        <circle cx="12" cy="12" r="3"></circle>
    </svg>
`;

const SVG_EYE_CLOSED = `
    <svg viewBox="0 0 24 24" width="16" height="16" stroke="currentColor" stroke-width="2.5" fill="none" stroke-linecap="round" stroke-linejoin="round">
        <path d="M17.94 17.94A10.07 10.07 0 0 1 12 20c-7 0-11-8-11-8a18.45 18.45 0 0 1 5.06-5.94M9.9 4.24A9.12 9.12 0 0 1 12 4c7 0 11 8 11 8a18.5 18.5 0 0 1-2.16 3.19m-6.72-1.07a3 3 0 1 1-4.24-4.24"></path>
        <line x1="1" y1="1" x2="23" y2="23"></line>
    </svg>
`;

// Add constraint row to list
function addConstraint(initialText = '', active = true) {
    const id = Date.now().toString() + Math.random().toString(36).substr(2, 5);
    const color = BOUNDARY_COLORS[state.constraints.length % BOUNDARY_COLORS.length];
    
    const constraint = {
        id,
        text: initialText,
        active,
        a: 0,
        b: 0,
        c: 0,
        operator: '<=',
        isStrict: false,
        error: false,
        color
    };
    
    state.constraints.push(constraint);
    
    // Render Constraint DOM Node
    const row = document.createElement('div');
    row.className = `ineq-item ${active ? '' : 'inactive'}`;
    row.id = `item-${id}`;
    row.innerHTML = `
        <button class="toggle-active-btn ${active ? 'active' : ''}" title="Bật/Tắt đường thẳng">
            ${active ? SVG_EYE_OPEN : SVG_EYE_CLOSED}
        </button>
        <div class="ineq-color-dot" style="color: ${color}; background-color: ${color}"></div>
        <div class="ineq-input-wrapper">
            <input type="text" class="ineq-input" placeholder="ví dụ: 3x + y <= 21" value="${initialText}">
            <div class="ineq-row-footer">
                <div class="operator-quick-btns">
                    <button class="op-btn" data-op="<=">&le;</button>
                    <button class="op-btn" data-op=">=">&ge;</button>
                    <button class="op-btn" data-op="<">&lt;</button>
                    <button class="op-btn" data-op=">">&gt;</button>
                </div>
                <div class="ineq-intercepts" id="intercepts-${id}"></div>
            </div>
        </div>
        <button class="delete-btn" title="Xóa">
            <svg viewBox="0 0 24 24" width="16" height="16" stroke="currentColor" stroke-width="2.5" fill="none" stroke-linecap="round" stroke-linejoin="round">
                <polyline points="3 6 5 6 21 6"></polyline>
                <path d="M19 6v14a2 2 0 0 1-2 2H7a2 2 0 0 1-2-2V6m3 0V4a2 2 0 0 1 2-2h4a2 2 0 0 1 2 2v2"></path>
                <line x1="10" y1="11" x2="10" y2="17"></line>
                <line x1="14" y1="11" x2="14" y2="17"></line>
            </svg>
        </button>
    `;
    
    els.inequalitiesList.appendChild(row);
    
    const input = row.querySelector('.ineq-input');
    const deleteBtn = row.querySelector('.delete-btn');
    const toggleActiveBtn = row.querySelector('.toggle-active-btn');
    const opBtns = row.querySelectorAll('.op-btn');
    
    // Toggle active click listener
    toggleActiveBtn.addEventListener('click', () => {
        constraint.active = !constraint.active;
        if (constraint.active) {
            toggleActiveBtn.classList.add('active');
            toggleActiveBtn.innerHTML = SVG_EYE_OPEN;
            row.classList.remove('inactive');
        } else {
            toggleActiveBtn.classList.remove('active');
            toggleActiveBtn.innerHTML = SVG_EYE_CLOSED;
            row.classList.add('inactive');
        }
        updateAppCalculations();
    });
    
    // Quick operator buttons click listeners
    opBtns.forEach(btn => {
        btn.addEventListener('click', (e) => {
            e.preventDefault();
            const op = btn.dataset.op;
            
            const start = input.selectionStart;
            const end = input.selectionEnd;
            const text = input.value;
            
            const before = text.substring(0, start);
            const after = text.substring(end, text.length);
            
            input.value = before + op + after;
            input.focus();
            
            const newPos = start + op.length;
            input.setSelectionRange(newPos, newPos);
            
            // Trigger input parsing
            updateConstraintText(id, input.value);
        });
    });
    
    // Input key listener
    input.addEventListener('input', (e) => {
        updateConstraintText(id, e.target.value);
    });
    
    // Delete action
    deleteBtn.addEventListener('click', () => {
        deleteConstraint(id);
    });
    
    // Focus in trigger validation highlight
    if (initialText) {
        updateConstraintText(id, initialText);
    } else {
        // Auto scroll & focus new input if user clicked "+ Thêm"
        setTimeout(() => {
            input.focus();
            els.inequalitiesList.scrollTop = els.inequalitiesList.scrollHeight;
            
            // Scroll sidebar so this section is visible
            const sidebar = document.querySelector('.sidebar');
            if (sidebar) {
                const section = row.closest('.inequalities-section');
                if (section) {
                    sidebar.scrollTop = section.offsetTop - 20;
                }
            }
        }, 50);
    }
}

function updateConstraintText(id, text) {
    const idx = state.constraints.findIndex(c => c.id === id);
    if (idx === -1) return;
    
    state.constraints[idx].text = text;
    const rowEl = document.getElementById(`item-${id}`);
    const interceptsEl = document.getElementById(`intercepts-${id}`);
    
    if (text.trim() === '') {
        state.constraints[idx].a = 0;
        state.constraints[idx].b = 0;
        state.constraints[idx].c = 0;
        state.constraints[idx].error = false;
        rowEl.classList.remove('has-error');
        if (interceptsEl) interceptsEl.textContent = '';
        updateAppCalculations();
        return;
    }
    
    try {
        const parsed = InequalityParser.parse(text);
        Object.assign(state.constraints[idx], parsed);
        state.constraints[idx].error = false;
        rowEl.classList.remove('has-error');
        rowEl.title = "";
        
        // Display intercepts
        if (interceptsEl) {
            const c = state.constraints[idx];
            const inters = getIntercepts(c);
            let labels = [];
            
            if (inters.x) {
                labels.push(`Ox: (${formatNum(inters.x.x)}; 0)`);
            } else {
                labels.push(`Ox: Ø`);
            }
            
            if (inters.y) {
                labels.push(`Oy: (0; ${formatNum(inters.y.y)})`);
            } else {
                labels.push(`Oy: Ø`);
            }
            
            interceptsEl.textContent = labels.join(' | ');
        }
    } catch (err) {
        state.constraints[idx].error = true;
        rowEl.classList.add('has-error');
        rowEl.title = err.message;
        if (interceptsEl) interceptsEl.textContent = '';
    }
    
    updateAppCalculations();
}

function deleteConstraint(id) {
    state.constraints = state.constraints.filter(c => c.id !== id);
    const el = document.getElementById(`item-${id}`);
    if (el) el.remove();
    updateAppCalculations();
}

function clearAllConstraints() {
    state.constraints = [];
    els.inequalitiesList.innerHTML = '';
}

// Presets Config Loader
const PRESETS = {
    'user-example': [
        'x >= 0',
        'y >= 0',
        '3x + y <= 21',
        'x + y <= 9'
    ],
    'bounded-polygon': [
        'x >= 1',
        'y >= 2',
        '2x + y <= 12',
        'x + 3y <= 18'
    ],
    'unbounded': [
        'x + y >= 4',
        '-x + 2y >= 2',
        'y <= 6'
    ],
    'no-solution': [
        'x + y <= 3',
        'x + y >= 6',
        'x >= 0',
        'y >= 0'
    ]
};

function loadPreset(name) {
    const list = PRESETS[name];
    if (!list) return;
    
    clearAllConstraints();
    list.forEach(eq => addConstraint(eq));
    
    // Auto scale and center depending on preset
    if (name === 'user-example') {
        fitViewToBounds(-1, 9, -1, 10);
    } else if (name === 'bounded-polygon') {
        fitViewToBounds(-1, 7, -1, 7);
    } else if (name === 'unbounded') {
        fitViewToBounds(-2, 10, -2, 8);
    } else {
        fitViewToBounds(-1, 7, -1, 7);
    }
    
    updateAppCalculations();
}

// Update mathematics & UI views
function updateAppCalculations() {
    calculateVertices();
    updateVerticesTable();
    render();
}

// Update Sidebar Vertices Table DOM
function updateVerticesTable() {
    els.verticesTableBody.innerHTML = '';
    
    if (state.vertices.length === 0) {
        els.noVerticesMsg.style.display = 'block';
        return;
    }
    
    els.noVerticesMsg.style.display = 'none';
    
    const showLP = state.lpEnabled;
    const optimalIdx = getOptimalVertexIndex();
    
    state.vertices.forEach((v, idx) => {
        const label = String.fromCharCode(65 + idx);
        const row = document.createElement('tr');
        row.className = 'vertex-row';
        if (showLP && idx === optimalIdx) {
            row.classList.add('lp-optimal');
        }
        
        const fVal = showLP ? (state.lpObjective.a * v.x + state.lpObjective.b * v.y) : 0;
        
        row.innerHTML = `
            <td class="vertex-name">${label}</td>
            <td class="vertex-coord">(${formatNum(v.x)}; ${formatNum(v.y)})</td>
            <td class="lp-col lp-val">${showLP ? formatNum(fVal) : ''}</td>
        `;
        
        // Highlight on hover row
        row.addEventListener('mouseenter', () => {
            state.hoveredVertexIdx = idx;
            render();
        });
        row.addEventListener('mouseleave', () => {
            state.hoveredVertexIdx = null;
            render();
        });
        
        els.verticesTableBody.appendChild(row);
    });
}

// --- EVENT HANDLERS & INITIALIZATION ---

// Mouse and touch interaction for zoom and pan
function registerCanvasControls() {
    
    // Zoom on wheel scroll
    els.canvas.addEventListener('wheel', (e) => {
        e.preventDefault();
        const factor = e.deltaY < 0 ? 1.1 : 0.9;
        const rect = els.canvas.getBoundingClientRect();
        const sx = e.clientX - rect.left;
        const sy = e.clientY - rect.top;
        zoomAt(sx, sy, factor);
        updateAppCalculations();
    }, { passive: false });
    
    function zoomAt(sx, sy, factor) {
        const cx = toCartesianX(sx);
        const cy = toCartesianY(sy);
        state.zoom *= factor;
        state.zoom = Math.max(5, Math.min(2000, state.zoom)); // limits
        state.panOffset.x = sx - (state.canvasSize.width / 2) - cx * state.zoom;
        state.panOffset.y = (state.canvasSize.height / 2) - sy + cy * state.zoom;
    }
    
    // Mouse dragging for pan
    els.canvas.addEventListener('mousedown', (e) => {
        state.isPanning = true;
        state.panStart.x = e.clientX - state.panOffset.x;
        state.panStart.y = e.clientY - state.panOffset.y;
    });
    
    window.addEventListener('mousemove', (e) => {
        const rect = els.canvas.getBoundingClientRect();
        const sx = e.clientX - rect.left;
        const sy = e.clientY - rect.top;
        
        // Show coordinates overlay
        if (sx >= 0 && sx <= state.canvasSize.width && sy >= 0 && sy <= state.canvasSize.height) {
            const cx = toCartesianX(sx);
            const cy = toCartesianY(sy);
            els.coordBadge.textContent = `x: ${formatNum(cx)}, y: ${formatNum(cy)}`;
        }
        
        if (!state.isPanning) {
            // Check if hovering over a vertex
            let hoveredIdx = null;
            const threshold = 8; // pixel threshold for hover detection
            state.vertices.forEach((v, idx) => {
                const screenVx = toScreenX(v.x);
                const screenVy = toScreenY(v.y);
                const dist = Math.hypot(sx - screenVx, sy - screenVy);
                if (dist < threshold) {
                    hoveredIdx = idx;
                }
            });
            
            if (hoveredIdx !== state.hoveredVertexIdx) {
                state.hoveredVertexIdx = hoveredIdx;
                render();
            }
            return;
        }
        
        state.panOffset.x = e.clientX - state.panStart.x;
        state.panOffset.y = e.clientY - state.panStart.y;
        render();
    });
    
    window.addEventListener('mouseup', () => {
        state.isPanning = false;
    });
    
    // Zoom control buttons
    els.zoomInBtn.addEventListener('click', () => {
        const centerX = state.canvasSize.width / 2;
        const centerY = state.canvasSize.height / 2;
        zoomAt(centerX, centerY, 1.25);
        updateAppCalculations();
    });
    
    els.zoomOutBtn.addEventListener('click', () => {
        const centerX = state.canvasSize.width / 2;
        const centerY = state.canvasSize.height / 2;
        zoomAt(centerX, centerY, 0.8);
        updateAppCalculations();
    });
    
    els.resetViewBtn.addEventListener('click', () => {
        // Find if user preset is active
        const activePresetBtn = document.querySelector('.preset-btn.active');
        const activePreset = activePresetBtn ? activePresetBtn.dataset.preset : 'user-example';
        
        if (activePreset === 'user-example') {
            fitViewToBounds(-1, 9, -1, 10);
        } else if (activePreset === 'bounded-polygon') {
            fitViewToBounds(-1, 7, -1, 7);
        } else if (activePreset === 'unbounded') {
            fitViewToBounds(-2, 10, -2, 8);
        } else {
            fitViewToBounds(-1, 7, -1, 7);
        }
        updateAppCalculations();
    });
    
    // Export chart image
    els.exportBtn.addEventListener('click', () => {
        const link = document.createElement('a');
        link.download = 'OxyGraph-MienNghiem.png';
        
        // Paint dynamic export canvas to preserve canvas sizing
        link.href = els.canvas.toDataURL('image/png');
        link.click();
    });
}

function initEventHandlers() {
    // Add inequality button
    els.addIneqBtn.addEventListener('click', () => {
        addConstraint('');
    });
    
    // LP toggle handler
    els.lpToggle.addEventListener('change', (e) => {
        state.lpEnabled = e.target.checked;
        if (state.lpEnabled) {
            els.lpContainer.classList.remove('disabled');
            document.querySelector('.results-table').classList.add('lp-active');
        } else {
            els.lpContainer.classList.add('disabled');
            document.querySelector('.results-table').classList.remove('lp-active');
        }
        updateAppCalculations();
    });
    
    // LP coefficients listeners
    const triggerLPUpdate = () => {
        state.lpObjective.a = parseFloat(els.lpA.value) || 0;
        state.lpObjective.b = parseFloat(els.lpB.value) || 0;
        updateAppCalculations();
    };
    
    els.lpA.addEventListener('input', triggerLPUpdate);
    els.lpB.addEventListener('input', triggerLPUpdate);
    
    // LP optimization type radio listeners
    els.lpOptTypes.forEach(radio => {
        radio.addEventListener('change', (e) => {
            state.lpObjective.optType = e.target.value;
            updateAppCalculations();
        });
    });
    
    // Preset buttons clicks
    els.presetBtns.forEach(btn => {
        btn.addEventListener('click', () => {
            els.presetBtns.forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            
            const presetName = btn.dataset.preset;
            loadPreset(presetName);
        });
    });
    
    // Handle window resize dynamically
    window.addEventListener('resize', () => {
        render();
    });
}

// App Initialization entry point
function initApp() {
    registerCanvasControls();
    initEventHandlers();
    
    // Load default preset (user example requested: 3x+y<=21, x+y<=9, x>=0, y>=0)
    loadPreset('user-example');
    
    // Keep animation loop for pulsing LP optimal node
    function animate() {
        if (state.lpEnabled) {
            render();
        }
        requestAnimationFrame(animate);
    }
    requestAnimationFrame(animate);
}

// Run on page loaded
document.addEventListener('DOMContentLoaded', () => {
    initApp();
});
