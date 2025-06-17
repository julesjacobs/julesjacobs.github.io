// Initialize Reveal.js
Reveal.initialize({
    hash: true,
    controls: true,
    progress: true,
    center: false,
    keyboard: true,
    overview: true,
    transition: 'slide',
    transitionSpeed: 'default',
    
    math: {
        mathjax: 'https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-mml-chtml.min.js',
        config: 'TeX-AMS_CHTML',
        tex: {
            inlineMath: [['$', '$'], ['\\(', '\\)']],
            displayMath: [['$$', '$$'], ['\\[', '\\]']],
            processEscapes: true,
            processEnvironments: true
        }
    },
    
    plugins: [ RevealMath, RevealHighlight, RevealNotes, RevealSearch ]
});

// Lazy load iframe
Reveal.on('slidechanged', event => {
    const iframe = event.currentSlide.querySelector('iframe[data-src]');
    if (iframe && !iframe.src) {
        iframe.src = iframe.getAttribute('data-src');
    }
});

// Packet Animation
class PacketAnimation {
    constructor() {
        this.switches = [
            // Left edge switches (sources) - green rectangles
            { id: 'H1', x: 125, y: 70, color: '#27ae60', hosts: ['10.0.0.1', '10.0.0.2'], edge: 'left' },
            { id: 'H2', x: 125, y: 175, color: '#27ae60', hosts: ['10.0.0.3', '10.0.0.4'], edge: 'left' },
            { id: 'H3', x: 125, y: 280, color: '#27ae60', hosts: ['10.0.0.5'], edge: 'left' },
            
            // Core switches - blue circles
            { id: 'S1', x: 275, y: 100, color: '#3498db', hosts: [] },
            { id: 'S2', x: 275, y: 250, color: '#3498db', hosts: [] },
            { id: 'S3', x: 425, y: 70, color: '#3498db', hosts: [] },
            { id: 'S4', x: 425, y: 175, color: '#3498db', hosts: [] },
            { id: 'S5', x: 425, y: 280, color: '#3498db', hosts: [] },
            { id: 'S6', x: 575, y: 100, color: '#3498db', hosts: [] },
            { id: 'S7', x: 575, y: 250, color: '#3498db', hosts: [] },
            
            // Right edge switches (destinations) - green rectangles
            { id: 'H4', x: 725, y: 70, color: '#27ae60', hosts: ['10.0.0.101', '10.0.0.102'], edge: 'right' },
            { id: 'H5', x: 725, y: 175, color: '#27ae60', hosts: ['10.0.0.103', '10.0.0.104'], edge: 'right' },
            { id: 'H6', x: 725, y: 280, color: '#27ae60', hosts: ['10.0.0.105'], edge: 'right' }
        ];
        
        this.links = [
            // Left edge to first core layer
            ['H1', 'S1'], ['H2', 'S1'], ['H2', 'S2'], ['H3', 'S2'],
            
            // First core to middle core
            ['S1', 'S3'], ['S1', 'S4'], ['S2', 'S4'], ['S2', 'S5'],
            
            // Middle core interconnects
            ['S3', 'S4'], ['S4', 'S5'],
            
            // Middle core to last core
            ['S3', 'S6'], ['S4', 'S6'], ['S4', 'S7'], ['S5', 'S7'],
            
            // Last core to right edge
            ['S6', 'H4'], ['S6', 'H5'], ['S7', 'H5'], ['S7', 'H6']
        ];
        
        this.currentPacket = null;
        this.animationState = 'idle';
        this.animationStartTime = 0;
        this.currentHopIndex = 0;
        this.path = [];
        
        this.miniPacket = null;
        this.largePacket = null;
        this.svg = null;
        
        this.initialized = false;
        
        // Animation state flags
        this.highlightApplied = false;
        this.valuesUpdated = false;
        this.highlightRemoved = false;
        this.vlanWillChange = false;
    }
    
    init() {
        if (this.initialized) return;
        this.initialized = true;
        
        this.svg = document.getElementById('network-svg');
        this.miniPacket = document.getElementById('mini-packet');
        this.largePacket = document.getElementById('large-packet');
        
        if (!this.svg || !this.miniPacket || !this.largePacket) {
            console.warn('Packet animation elements not found');
            return;
        }
        
        this.drawNetwork();
        this.startAnimation();
    }
    
    drawNetwork() {
        // Clear SVG and network-viz children (except svg and packets)
        this.svg.innerHTML = '';
        const networkViz = document.getElementById('network-viz');
        const elementsToRemove = networkViz.querySelectorAll('.network-switch, .network-host');
        elementsToRemove.forEach(el => el.remove());
        
        // Draw links
        this.links.forEach(link => {
            const source = this.switches.find(s => s.id === link[0]);
            const target = this.switches.find(s => s.id === link[1]);
            
            const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
            path.setAttribute('d', `M ${source.x} ${source.y} L ${target.x} ${target.y}`);
            path.setAttribute('class', 'link');
            this.svg.appendChild(path);
        });
        
        // Draw switches and hosts
        this.switches.forEach(sw => {
            const container = document.createElement('div');
            container.className = sw.edge ? 'network-host' : 'network-switch';
            container.style.left = sw.x + 'px';
            container.style.top = sw.y + 'px';
            
            // Create SVG element
            const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
            svg.setAttribute('width', '70');
            svg.setAttribute('height', '70');
            svg.setAttribute('viewBox', '0 0 70 70');
            
            if (sw.edge) {
                // Draw host (computer) icon
                // Monitor screen
                const monitor = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                monitor.setAttribute('x', '10');
                monitor.setAttribute('y', '15');
                monitor.setAttribute('width', '50');
                monitor.setAttribute('height', '35');
                monitor.setAttribute('rx', '2');
                monitor.setAttribute('fill', '#27ae60');
                monitor.setAttribute('stroke', '#229954');
                monitor.setAttribute('stroke-width', '2');
                
                // Monitor screen inner
                const screen = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                screen.setAttribute('x', '15');
                screen.setAttribute('y', '20');
                screen.setAttribute('width', '40');
                screen.setAttribute('height', '25');
                screen.setAttribute('fill', '#229954');
                
                // Monitor stand
                const stand = document.createElementNS('http://www.w3.org/2000/svg', 'path');
                stand.setAttribute('d', 'M 30 50 L 40 50 L 38 55 L 32 55 Z');
                stand.setAttribute('fill', '#27ae60');
                stand.setAttribute('stroke', '#229954');
                stand.setAttribute('stroke-width', '1');
                
                // Monitor base
                const base = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                base.setAttribute('x', '25');
                base.setAttribute('y', '55');
                base.setAttribute('width', '20');
                base.setAttribute('height', '3');
                base.setAttribute('rx', '1');
                base.setAttribute('fill', '#229954');
                
                svg.appendChild(monitor);
                svg.appendChild(screen);
                svg.appendChild(stand);
                svg.appendChild(base);
                
                // Add host name as text on screen
                const hostText = document.createElementNS('http://www.w3.org/2000/svg', 'text');
                hostText.setAttribute('x', '35');
                hostText.setAttribute('y', '35');
                hostText.setAttribute('text-anchor', 'middle');
                hostText.setAttribute('font-size', '12');
                hostText.setAttribute('font-family', 'monospace');
                hostText.setAttribute('font-weight', 'bold');
                hostText.setAttribute('fill', '#ffffff');
                hostText.textContent = sw.id;
                svg.appendChild(hostText);
            } else {
                // Draw switch as simple blue circle
                const bgCircle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
                bgCircle.setAttribute('cx', '35');
                bgCircle.setAttribute('cy', '35');
                bgCircle.setAttribute('r', '22');
                bgCircle.setAttribute('fill', '#3498db');
                bgCircle.setAttribute('stroke', '#2980b9');
                bgCircle.setAttribute('stroke-width', '2');
                svg.appendChild(bgCircle);
                
                // Switch name
                const switchText = document.createElementNS('http://www.w3.org/2000/svg', 'text');
                switchText.setAttribute('x', '35');
                switchText.setAttribute('y', '40');
                switchText.setAttribute('text-anchor', 'middle');
                switchText.setAttribute('font-size', '14');
                switchText.setAttribute('font-family', 'Arial, sans-serif');
                switchText.setAttribute('font-weight', 'bold');
                switchText.setAttribute('fill', '#ffffff');
                switchText.textContent = sw.id;
                svg.appendChild(switchText);
            }
            
            container.appendChild(svg);
            
            networkViz.appendChild(container);
        });
    }
    
    generatePacket() {
        const leftHosts = this.switches.filter(s => s.edge === 'left').flatMap(s => s.hosts);
        const rightHosts = this.switches.filter(s => s.edge === 'right').flatMap(s => s.hosts);
        
        const src = leftHosts[Math.floor(Math.random() * leftHosts.length)];
        const dst = rightHosts[Math.floor(Math.random() * rightHosts.length)];
        
        const srcSwitch = this.switches.find(s => s.hosts.includes(src));
        const dstSwitch = this.switches.find(s => s.hosts.includes(dst));
        
        this.currentPacket = {
            src: src,
            dst: dst,
            port: Math.floor(Math.random() * 65536),
            vlan: Math.floor(Math.random() * 4096),
            ttl: 64,
            switch: srcSwitch.id
        };
        
        // Calculate path (simplified - in real implementation would use Dijkstra)
        this.path = this.calculatePath(srcSwitch.id, dstSwitch.id);
        this.currentHopIndex = 0;
    }
    
    calculatePath(srcId, dstId) {
        // Simplified path calculation
        // In a real implementation, this would use a proper pathfinding algorithm
        const paths = {
            'H1-H4': ['H1', 'S1', 'S3', 'S6', 'H4'],
            'H1-H5': ['H1', 'S1', 'S4', 'S6', 'H5'],
            'H1-H6': ['H1', 'S1', 'S4', 'S7', 'H6'],
            'H2-H4': ['H2', 'S1', 'S3', 'S6', 'H4'],
            'H2-H5': ['H2', 'S2', 'S4', 'S7', 'H5'],
            'H2-H6': ['H2', 'S2', 'S5', 'S7', 'H6'],
            'H3-H4': ['H3', 'S2', 'S4', 'S6', 'H4'],
            'H3-H5': ['H3', 'S2', 'S4', 'S6', 'H5'],
            'H3-H6': ['H3', 'S2', 'S5', 'S7', 'H6']
        };
        
        const key = `${srcId}-${dstId}`;
        return paths[key] || [srcId, 'S1', 'S3', 'S6', dstId];
    }
    
    updatePacketDisplay() {
        document.getElementById('field-src').textContent = this.currentPacket.src;
        document.getElementById('field-dst').textContent = this.currentPacket.dst;
        document.getElementById('field-port').textContent = this.currentPacket.port;
        document.getElementById('field-vlan').textContent = this.currentPacket.vlan;
        document.getElementById('field-ttl').textContent = this.currentPacket.ttl;
        document.getElementById('field-switch').textContent = this.currentPacket.switch;
    }
    
    
    highlightFields(fields) {
        fields.forEach(fieldName => {
            // Highlight large packet field
            const field = document.querySelector(`.field[data-field="${fieldName}"]`);
            if (field) field.classList.add('highlight');
            
            // Highlight mini packet field
            const miniField = document.querySelector(`.mini-packet-field.${fieldName}`);
            if (miniField) miniField.classList.add('highlight');
        });
    }
    
    unhighlightFields() {
        document.querySelectorAll('.field.highlight').forEach(field => {
            field.classList.remove('highlight');
        });
        document.querySelectorAll('.mini-packet-field.highlight').forEach(field => {
            field.classList.remove('highlight');
        });
    }
    
    animate(timestamp) {
        if (!this.initialized) return;
        
        const elapsed = timestamp - this.animationStartTime;
        
        switch (this.animationState) {
            case 'idle':
                this.generatePacket();
                this.animationState = 'arrival';
                this.animationStartTime = timestamp;
                break;
                
            case 'arrival':
                if (elapsed < 500) {
                    const opacity = elapsed / 500;
                    this.miniPacket.style.opacity = opacity;
                    this.largePacket.style.opacity = opacity;
                    
                    if (elapsed <= 16) { // First frame
                        const startSwitch = this.switches.find(s => s.id === this.path[0]);
                        this.miniPacket.style.left = startSwitch.x + 'px';
                        this.miniPacket.style.top = startSwitch.y + 'px';
                        this.updatePacketDisplay();
                    }
                } else {
                    this.miniPacket.style.opacity = 1;
                    this.largePacket.style.opacity = 1;
                    this.animationState = 'movement';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'movement':
                if (this.currentHopIndex < this.path.length - 1) {
                    if (elapsed < 1500) {
                        const progress = elapsed / 1500;
                        const currentSwitch = this.switches.find(s => s.id === this.path[this.currentHopIndex]);
                        const nextSwitch = this.switches.find(s => s.id === this.path[this.currentHopIndex + 1]);
                        
                        const x = currentSwitch.x + (nextSwitch.x - currentSwitch.x) * progress;
                        const y = currentSwitch.y + (nextSwitch.y - currentSwitch.y) * progress;
                        
                        this.miniPacket.style.left = x + 'px';
                        this.miniPacket.style.top = y + 'px';
                    } else {
                        this.currentHopIndex++;
                        this.animationState = 'pause';
                        this.animationStartTime = timestamp;
                    }
                } else {
                    this.animationState = 'departure';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'pause':
                if (elapsed < 200) {
                    // Just wait
                } else if (elapsed < 400) {
                    // Highlight fields that will change
                    if (elapsed >= 200 && !this.highlightApplied) {
                        const fieldsToHighlight = ['switch', 'ttl'];
                        this.vlanWillChange = Math.random() < 0.3;
                        if (this.vlanWillChange) fieldsToHighlight.push('vlan');
                        this.highlightFields(fieldsToHighlight);
                        this.highlightApplied = true;
                    }
                } else if (elapsed >= 400 && !this.valuesUpdated) {
                    // Update values
                    this.currentPacket.switch = this.path[this.currentHopIndex];
                    this.currentPacket.ttl--;
                    if (this.vlanWillChange) {
                        this.currentPacket.vlan = Math.floor(Math.random() * 4096);
                    }
                    this.updatePacketDisplay();
                    this.valuesUpdated = true;
                } else if (elapsed < 600) {
                    // Keep highlights
                } else if (elapsed >= 600 && !this.highlightRemoved) {
                    // Remove highlights
                    this.unhighlightFields();
                    this.highlightRemoved = true;
                } else if (elapsed >= 800) {
                    // Reset flags and move to next state
                    this.highlightApplied = false;
                    this.valuesUpdated = false;
                    this.highlightRemoved = false;
                    this.animationState = 'movement';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'departure':
                if (elapsed < 500) {
                    const opacity = 1 - (elapsed / 500);
                    this.miniPacket.style.opacity = opacity;
                    this.largePacket.style.opacity = opacity;
                } else {
                    this.miniPacket.style.opacity = 0;
                    this.largePacket.style.opacity = 0;
                    this.animationState = 'idle';
                    this.animationStartTime = timestamp;
                }
                break;
        }
        
        requestAnimationFrame(this.animate.bind(this));
    }
    
    startAnimation() {
        requestAnimationFrame(this.animate.bind(this));
    }
}

// Initialize packet animation when slide is shown
const packetAnimation = new PacketAnimation();

Reveal.on('slidechanged', event => {
    if (event.currentSlide.querySelector('.packet-animation')) {
        packetAnimation.init();
    }
});

// Also initialize if we start on the animation slide
if (document.querySelector('.present .packet-animation')) {
    packetAnimation.init();
}

// StacKAT Packet Animation with Payload
class StackATPacketAnimation {
    constructor() {
        this.switches = [
            // Left edge switches (sources) - green rectangles
            { id: 'H1', x: 125, y: 70, color: '#27ae60', hosts: ['10.0.0.1', '10.0.0.2'], edge: 'left' },
            { id: 'H2', x: 125, y: 175, color: '#27ae60', hosts: ['10.0.0.3', '10.0.0.4'], edge: 'left' },
            { id: 'H3', x: 125, y: 280, color: '#27ae60', hosts: ['10.0.0.5'], edge: 'left' },
            
            // Core switches - blue circles
            { id: 'S1', x: 275, y: 100, color: '#3498db', hosts: [] },
            { id: 'S2', x: 275, y: 250, color: '#3498db', hosts: [] },
            { id: 'S3', x: 425, y: 70, color: '#3498db', hosts: [] },
            { id: 'S4', x: 425, y: 175, color: '#3498db', hosts: [] },
            { id: 'S5', x: 425, y: 280, color: '#3498db', hosts: [] },
            { id: 'S6', x: 575, y: 100, color: '#3498db', hosts: [] },
            { id: 'S7', x: 575, y: 250, color: '#3498db', hosts: [] },
            
            // Right edge switches (destinations) - green rectangles
            { id: 'H4', x: 725, y: 70, color: '#27ae60', hosts: ['10.0.0.101', '10.0.0.102'], edge: 'right' },
            { id: 'H5', x: 725, y: 175, color: '#27ae60', hosts: ['10.0.0.103', '10.0.0.104'], edge: 'right' },
            { id: 'H6', x: 725, y: 280, color: '#27ae60', hosts: ['10.0.0.105'], edge: 'right' }
        ];
        
        this.links = [
            // Left edge to first core layer
            ['H1', 'S1'], ['H2', 'S1'], ['H2', 'S2'], ['H3', 'S2'],
            
            // First core to middle core
            ['S1', 'S3'], ['S1', 'S4'], ['S2', 'S4'], ['S2', 'S5'],
            
            // Middle core interconnects
            ['S3', 'S4'], ['S4', 'S5'],
            
            // Middle core to last core
            ['S3', 'S6'], ['S4', 'S6'], ['S4', 'S7'], ['S5', 'S7'],
            
            // Last core to right edge
            ['S6', 'H4'], ['S6', 'H5'], ['S7', 'H5'], ['S7', 'H6']
        ];
        
        this.currentPacket = null;
        this.animationState = 'idle';
        this.animationStartTime = 0;
        this.currentHopIndex = 0;
        this.path = [];
        
        this.miniPacket = null;
        this.largePacket = null;
        this.svg = null;
        
        this.initialized = false;
        
        // Animation state flags
        this.highlightApplied = false;
        this.valuesUpdated = false;
        this.highlightRemoved = false;
        this.vlanWillChange = false;
        this.payloadWillChange = false;
        
        // Initial payload pattern
        this.basePayload = '101010';
    }
    
    // Push bits to the front of the payload
    pushBits(payload, bits) {
        return bits + payload;
    }
    
    // Pop bits from the front of the payload
    popBits(payload, count) {
        return payload.substring(count);
    }
    
    // Transform payload at each hop
    transformPayload(payload) {
        // Randomly decide to push or pop bits
        const operation = Math.random() < 0.5 ? 'push' : 'pop';
        
        if (operation === 'push') {
            // Push 1-3 random bits to the front
            const bitCount = Math.floor(Math.random() * 3) + 1;
            const newBits = Array.from({length: bitCount}, () => Math.random() < 0.5 ? '1' : '0').join('');
            return this.pushBits(payload, newBits);
        } else {
            // Pop 1-3 bits from the front (but keep at least 4 bits)
            const maxPop = Math.min(3, payload.length - 4);
            if (maxPop > 0) {
                const popCount = Math.floor(Math.random() * maxPop) + 1;
                return this.popBits(payload, popCount);
            }
            // If payload is too short, push instead
            const newBit = Math.random() < 0.5 ? '1' : '0';
            return this.pushBits(payload, newBit);
        }
    }
    
    init() {
        if (this.initialized) return;
        this.initialized = true;
        
        this.svg = document.getElementById('network-svg-stackat');
        this.miniPacket = document.getElementById('mini-packet-stackat');
        this.largePacket = document.getElementById('large-packet-stackat');
        
        if (!this.svg || !this.miniPacket || !this.largePacket) {
            console.warn('StacKAT packet animation elements not found');
            return;
        }
        
        this.drawNetwork();
        this.startAnimation();
    }
    
    drawNetwork() {
        // Clear SVG and network-viz children (except svg and packets)
        this.svg.innerHTML = '';
        const networkViz = document.getElementById('network-viz-stackat');
        const elementsToRemove = networkViz.querySelectorAll('.network-switch, .network-host');
        elementsToRemove.forEach(el => el.remove());
        
        // Draw links
        this.links.forEach(link => {
            const source = this.switches.find(s => s.id === link[0]);
            const target = this.switches.find(s => s.id === link[1]);
            
            const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
            path.setAttribute('d', `M ${source.x} ${source.y} L ${target.x} ${target.y}`);
            path.setAttribute('class', 'link');
            this.svg.appendChild(path);
        });
        
        // Draw switches and hosts
        this.switches.forEach(sw => {
            const container = document.createElement('div');
            container.className = sw.edge ? 'network-host' : 'network-switch';
            container.style.left = sw.x + 'px';
            container.style.top = sw.y + 'px';
            
            // Create SVG element
            const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
            svg.setAttribute('width', '70');
            svg.setAttribute('height', '70');
            svg.setAttribute('viewBox', '0 0 70 70');
            
            if (sw.edge) {
                // Draw host (computer) icon
                // Monitor screen
                const monitor = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                monitor.setAttribute('x', '10');
                monitor.setAttribute('y', '15');
                monitor.setAttribute('width', '50');
                monitor.setAttribute('height', '35');
                monitor.setAttribute('rx', '2');
                monitor.setAttribute('fill', '#27ae60');
                monitor.setAttribute('stroke', '#229954');
                monitor.setAttribute('stroke-width', '2');
                
                // Monitor screen inner
                const screen = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                screen.setAttribute('x', '15');
                screen.setAttribute('y', '20');
                screen.setAttribute('width', '40');
                screen.setAttribute('height', '25');
                screen.setAttribute('fill', '#229954');
                
                // Monitor stand
                const stand = document.createElementNS('http://www.w3.org/2000/svg', 'path');
                stand.setAttribute('d', 'M 30 50 L 40 50 L 38 55 L 32 55 Z');
                stand.setAttribute('fill', '#27ae60');
                stand.setAttribute('stroke', '#229954');
                stand.setAttribute('stroke-width', '1');
                
                // Monitor base
                const base = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                base.setAttribute('x', '25');
                base.setAttribute('y', '55');
                base.setAttribute('width', '20');
                base.setAttribute('height', '3');
                base.setAttribute('rx', '1');
                base.setAttribute('fill', '#229954');
                
                svg.appendChild(monitor);
                svg.appendChild(screen);
                svg.appendChild(stand);
                svg.appendChild(base);
                
                // Add host name as text on screen
                const hostText = document.createElementNS('http://www.w3.org/2000/svg', 'text');
                hostText.setAttribute('x', '35');
                hostText.setAttribute('y', '35');
                hostText.setAttribute('text-anchor', 'middle');
                hostText.setAttribute('font-size', '12');
                hostText.setAttribute('font-family', 'monospace');
                hostText.setAttribute('font-weight', 'bold');
                hostText.setAttribute('fill', '#ffffff');
                hostText.textContent = sw.id;
                svg.appendChild(hostText);
            } else {
                // Draw switch as simple blue circle
                const bgCircle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
                bgCircle.setAttribute('cx', '35');
                bgCircle.setAttribute('cy', '35');
                bgCircle.setAttribute('r', '22');
                bgCircle.setAttribute('fill', '#3498db');
                bgCircle.setAttribute('stroke', '#2980b9');
                bgCircle.setAttribute('stroke-width', '2');
                svg.appendChild(bgCircle);
                
                // Switch name
                const switchText = document.createElementNS('http://www.w3.org/2000/svg', 'text');
                switchText.setAttribute('x', '35');
                switchText.setAttribute('y', '40');
                switchText.setAttribute('text-anchor', 'middle');
                switchText.setAttribute('font-size', '14');
                switchText.setAttribute('font-family', 'Arial, sans-serif');
                switchText.setAttribute('font-weight', 'bold');
                switchText.setAttribute('fill', '#ffffff');
                switchText.textContent = sw.id;
                svg.appendChild(switchText);
            }
            
            container.appendChild(svg);
            
            networkViz.appendChild(container);
        });
    }
    
    generatePacket() {
        const leftHosts = this.switches.filter(s => s.edge === 'left').flatMap(s => s.hosts);
        const rightHosts = this.switches.filter(s => s.edge === 'right').flatMap(s => s.hosts);
        
        const src = leftHosts[Math.floor(Math.random() * leftHosts.length)];
        const dst = rightHosts[Math.floor(Math.random() * rightHosts.length)];
        
        const srcSwitch = this.switches.find(s => s.hosts.includes(src));
        const dstSwitch = this.switches.find(s => s.hosts.includes(dst));
        
        // Generate initial payload with some random bits added
        const randomBits = Array.from({length: 4}, () => Math.random() < 0.5 ? '1' : '0').join('');
        const initialPayload = this.basePayload + randomBits;
        
        this.currentPacket = {
            src: src,
            dst: dst,
            port: Math.floor(Math.random() * 65536),
            vlan: Math.floor(Math.random() * 4096),
            ttl: 64,
            switch: srcSwitch.id,
            payload: initialPayload
        };
        
        // Calculate path (simplified - in real implementation would use Dijkstra)
        this.path = this.calculatePath(srcSwitch.id, dstSwitch.id);
        this.currentHopIndex = 0;
    }
    
    calculatePath(srcId, dstId) {
        // Simplified path calculation
        // In a real implementation, this would use a proper pathfinding algorithm
        const paths = {
            'H1-H4': ['H1', 'S1', 'S3', 'S6', 'H4'],
            'H1-H5': ['H1', 'S1', 'S4', 'S6', 'H5'],
            'H1-H6': ['H1', 'S1', 'S4', 'S7', 'H6'],
            'H2-H4': ['H2', 'S1', 'S3', 'S6', 'H4'],
            'H2-H5': ['H2', 'S2', 'S4', 'S7', 'H5'],
            'H2-H6': ['H2', 'S2', 'S5', 'S7', 'H6'],
            'H3-H4': ['H3', 'S2', 'S4', 'S6', 'H4'],
            'H3-H5': ['H3', 'S2', 'S4', 'S6', 'H5'],
            'H3-H6': ['H3', 'S2', 'S5', 'S7', 'H6']
        };
        
        const key = `${srcId}-${dstId}`;
        return paths[key] || [srcId, 'S1', 'S3', 'S6', dstId];
    }
    
    updatePacketDisplay() {
        document.getElementById('field-src-stackat').textContent = this.currentPacket.src;
        document.getElementById('field-dst-stackat').textContent = this.currentPacket.dst;
        document.getElementById('field-port-stackat').textContent = this.currentPacket.port;
        document.getElementById('field-vlan-stackat').textContent = this.currentPacket.vlan;
        document.getElementById('field-ttl-stackat').textContent = this.currentPacket.ttl;
        document.getElementById('field-switch-stackat').textContent = this.currentPacket.switch;
        document.getElementById('field-payload-stackat').textContent = this.currentPacket.payload;
    }
    
    highlightFields(fields) {
        fields.forEach(fieldName => {
            // Highlight large packet field - scope to stackat container
            const field = document.querySelector(`.packet-fields-stackat .field[data-field="${fieldName}"]`);
            if (field) field.classList.add('highlight');
            
            // Highlight mini packet field - scope to stackat mini packet
            const miniField = document.querySelector(`#mini-packet-stackat .mini-packet-field.${fieldName}`);
            if (miniField) miniField.classList.add('highlight');
        });
    }
    
    unhighlightFields() {
        document.querySelectorAll('.packet-fields-stackat .field.highlight').forEach(field => {
            field.classList.remove('highlight');
        });
        document.querySelectorAll('#mini-packet-stackat .mini-packet-field.highlight').forEach(field => {
            field.classList.remove('highlight');
        });
    }
    
    animate(timestamp) {
        if (!this.initialized) return;
        
        const elapsed = timestamp - this.animationStartTime;
        
        switch (this.animationState) {
            case 'idle':
                this.generatePacket();
                this.animationState = 'arrival';
                this.animationStartTime = timestamp;
                break;
                
            case 'arrival':
                if (elapsed < 500) {
                    const opacity = elapsed / 500;
                    this.miniPacket.style.opacity = opacity;
                    this.largePacket.style.opacity = opacity;
                    
                    if (elapsed <= 16) { // First frame
                        const startSwitch = this.switches.find(s => s.id === this.path[0]);
                        this.miniPacket.style.left = startSwitch.x + 'px';
                        this.miniPacket.style.top = startSwitch.y + 'px';
                        this.updatePacketDisplay();
                    }
                } else {
                    this.miniPacket.style.opacity = 1;
                    this.largePacket.style.opacity = 1;
                    this.animationState = 'movement';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'movement':
                if (this.currentHopIndex < this.path.length - 1) {
                    if (elapsed < 1500) {
                        const progress = elapsed / 1500;
                        const currentSwitch = this.switches.find(s => s.id === this.path[this.currentHopIndex]);
                        const nextSwitch = this.switches.find(s => s.id === this.path[this.currentHopIndex + 1]);
                        
                        const x = currentSwitch.x + (nextSwitch.x - currentSwitch.x) * progress;
                        const y = currentSwitch.y + (nextSwitch.y - currentSwitch.y) * progress;
                        
                        this.miniPacket.style.left = x + 'px';
                        this.miniPacket.style.top = y + 'px';
                    } else {
                        this.currentHopIndex++;
                        this.animationState = 'pause';
                        this.animationStartTime = timestamp;
                    }
                } else {
                    this.animationState = 'departure';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'pause':
                if (elapsed < 200) {
                    // Just wait
                } else if (elapsed < 400) {
                    // Highlight fields that will change
                    if (elapsed >= 200 && !this.highlightApplied) {
                        this.vlanWillChange = Math.random() < 0.3;
                        this.payloadWillChange = true; // Always change payload
                        
                        const fieldsToHighlight = ['switch', 'ttl'];
                        if (this.vlanWillChange) fieldsToHighlight.push('vlan');
                        if (this.payloadWillChange) fieldsToHighlight.push('payload');
                        this.highlightFields(fieldsToHighlight);
                        this.highlightApplied = true;
                    }
                } else if (elapsed >= 400 && !this.valuesUpdated) {
                    // Update values
                    this.currentPacket.switch = this.path[this.currentHopIndex];
                    this.currentPacket.ttl--;
                    if (this.vlanWillChange) {
                        this.currentPacket.vlan = Math.floor(Math.random() * 4096);
                    }
                    if (this.payloadWillChange) {
                        this.currentPacket.payload = this.transformPayload(this.currentPacket.payload);
                    }
                    this.updatePacketDisplay();
                    this.valuesUpdated = true;
                } else if (elapsed < 600) {
                    // Keep highlights
                } else if (elapsed >= 600 && !this.highlightRemoved) {
                    // Remove highlights
                    this.unhighlightFields();
                    this.highlightRemoved = true;
                } else if (elapsed >= 800) {
                    // Reset flags and move to next state
                    this.highlightApplied = false;
                    this.valuesUpdated = false;
                    this.highlightRemoved = false;
                    this.animationState = 'movement';
                    this.animationStartTime = timestamp;
                }
                break;
                
            case 'departure':
                if (elapsed < 500) {
                    const opacity = 1 - (elapsed / 500);
                    this.miniPacket.style.opacity = opacity;
                    this.largePacket.style.opacity = opacity;
                } else {
                    this.miniPacket.style.opacity = 0;
                    this.largePacket.style.opacity = 0;
                    this.animationState = 'idle';
                    this.animationStartTime = timestamp;
                }
                break;
        }
        
        requestAnimationFrame(this.animate.bind(this));
    }
    
    startAnimation() {
        requestAnimationFrame(this.animate.bind(this));
    }
}

// Initialize StacKAT packet animation when slide is shown
const stackatPacketAnimation = new StackATPacketAnimation();

Reveal.on('slidechanged', event => {
    if (event.currentSlide.querySelector('.packet-animation-stackat')) {
        stackatPacketAnimation.init();
    }
});

// Also initialize if we start on the StacKAT animation slide
if (document.querySelector('.present .packet-animation-stackat')) {
    stackatPacketAnimation.init();
}